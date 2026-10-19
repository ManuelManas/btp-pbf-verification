#!/bin/sh
set -eu
cd "$(dirname "$0")"
if [ ! -d .deps/.lake/build/lib/lean/Mathlib ]; then
    printf '%s\n' 'Run python3 bootstrap.py first.' >&2
    exit 1
fi
# Each verification starts with an empty directory of local compiled modules.
BTP_BUILD_DIR=$(mktemp -d "$PWD/.verification.XXXXXX")
export BTP_BUILD_DIR
printf 'Fresh local build: %s\n' "$BTP_BUILD_DIR"
./run_lean.sh --version
while IFS= read -r btp_module; do
    printf '\nChecking %s.lean\n' "$btp_module"
    ./run_lean.sh -DwarningAsError=true -o "$BTP_BUILD_DIR/$btp_module.olean" "$btp_module.lean"
done < modules.txt
printf '\nAuditing every project theorem and its axiom dependencies\n'
./run_lean.sh -DwarningAsError=true AxiomAudit.lean
printf '\nVERIFIED: fresh build and all-theorem axiom audit passed.\n'
