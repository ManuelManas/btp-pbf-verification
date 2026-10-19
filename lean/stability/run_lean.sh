#!/bin/sh
set -eu
cd "$(dirname "$0")"
LEAN_PATH="${BTP_BUILD_DIR:-$PWD/.build}:$PWD/.deps/.lake/build/lib/lean"
for btp_dep in "$PWD"/.deps/.lake/packages/*/.lake/build/lib/lean; do
    if [ -d "$btp_dep" ]; then LEAN_PATH="$LEAN_PATH:$btp_dep"; fi
done
export LEAN_PATH
btp_default_lean="${ELAN_HOME:-$HOME/.elan}/toolchains/leanprover--lean4---v4.34.0-rc2/bin/lean"
if [ -n "${BTP_LEAN_BIN:-}" ]; then
    btp_lean="$BTP_LEAN_BIN"
elif [ -x "$btp_default_lean" ]; then
    btp_lean="$btp_default_lean"
else
    btp_lean=lean
fi
exec "$btp_lean" "$@"
