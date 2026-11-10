#!/usr/bin/env python3
"""Prepare the pinned, checksum-verified mathlib cache locally.

Only .deps/ and .cache/ inside this project are written. The existing
~/.cache/mathlib directory is read, never modified. No theorem is generated.
"""

import argparse
import concurrent.futures
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import urllib.error
import urllib.request

ROOT = Path(__file__).resolve().parent
MANIFEST = json.loads((ROOT / "cache-manifest.json").read_text())


def checked(path, expected):
    return path.is_file() and hashlib.sha256(path.read_bytes()).hexdigest() == expected


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--offline", action="store_true", help="use existing archives only")
    args = parser.parse_args()
    deps = ROOT / ".deps"
    if deps.is_symlink():
        if deps.is_dir():
            print("Using the shared local dependency cache; no dependency files modified. Run ./check.sh.")
            return
        deps.unlink()
    local_cache = ROOT / ".cache"
    local_cache.mkdir(exist_ok=True)
    shared_cache = Path.home() / ".cache" / "mathlib"

    def obtain(item):
        name, expected = item["archive"], item["sha256"]
        for candidate in (shared_cache / name, local_cache / name):
            if checked(candidate, expected):
                return candidate
        if args.offline:
            raise RuntimeError("Missing verified cache archive: " + name)
        temp = local_cache / (name + ".download")
        for container in ("mathlib4-master", "mathlib4"):
            url = f"https://lakecache.blob.core.windows.net/{container}/f/{name}"
            try:
                with urllib.request.urlopen(url, timeout=60) as response:
                    temp.write_bytes(response.read())
            except urllib.error.HTTPError as exc:
                if exc.code == 404:
                    continue
                raise
            if not checked(temp, expected):
                raise RuntimeError("SHA256 mismatch: " + name)
            dest = local_cache / name
            temp.replace(dest)
            return dest
        raise RuntimeError("Archive unavailable from the pinned cache: " + name)

    toolchain = MANIFEST["lean"].replace("/", "--").replace(":", "---")
    elan_home = Path(os.environ.get("ELAN_HOME", str(Path.home() / ".elan")))
    bundled = elan_home / "toolchains" / toolchain / "bin" / "leantar"
    leantar = os.environ.get("BTP_LEANTAR") or (str(bundled) if bundled.is_file()
                                               else shutil.which("leantar"))
    if not leantar:
        raise SystemExit("Install the toolchain in lean-toolchain first (elan toolchain install).")
    with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
        archives = list(pool.map(obtain, MANIFEST["modules"]))
    deps.mkdir(exist_ok=True)
    subprocess.run([leantar, "-C", str(deps), "-f", "-x", "-"],
                   input="\n".join(map(str, archives)), text=True, check=True)
    # A missing cache archive is compiled from its checksum-verified pinned source.
    lean = os.environ.get("BTP_LEAN_BIN") or str(Path(leantar).with_name("lean"))
    paths = [deps / ".lake/build/lib/lean"]
    paths.extend(sorted((deps / ".lake/packages").glob("*/.lake/build/lib/lean")))
    env = os.environ.copy()
    env["LEAN_PATH"] = ":".join(map(str, paths))
    for item in MANIFEST.get("source_modules", []):
        src = ROOT / item["source"]
        if not checked(src, item["sha256"]):
            raise RuntimeError("Pinned source checksum mismatch: " + item["module"])
        rel = Path(item["module"].replace(".", "/") + ".lean")
        output = deps / ".lake/build/lib/lean" / rel.with_suffix(".olean")
        output.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run([lean, "-o", str(output), str(rel)],
                       cwd=ROOT / "dependency_sources", env=env, check=True)
    print(f"Verified {len(archives)} dependency archives and compiled pinned source exceptions. Run ./check.sh.")


if __name__ == "__main__":
    main()
