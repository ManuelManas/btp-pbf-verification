BTP/PBF verification — v64 — 13 October 2026

README.md gives the reproduction instructions and contents.
verification_v64/LEAN_CORRESPONDENCE_v64.txt maps manuscript statements
to formal theorem names and explains the index conventions.

v64 adds the exact constant mathfrak B in Lemma 2.16. Its proof is in
lean/semi_infinite/SharpUniformMinors.lean. CompleteSharpResults.lean
assembles the identities, zero-row boundary case and uniform bound.
All 28 modules in that project were checked in a fresh build directory.
The log and validation record are in verification_v64/.

The 68 Lean sources of v48 are retained unchanged, and two are added.
The Toeplitz project remains unchanged. Run bootstrap.py and check.sh
in each Lean project to reproduce its full build, using the pinned toolchain.
Python checks and their existing run records are in computational/.
