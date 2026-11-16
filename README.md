# BTP/PBF verification

Companion data and proofs for *Banded Totally Positive Matrices and Positive Bidiagonal Factorizations: Existence, Stability, and Toeplitz Orthogonality*, by Manuel Mañas.

**[Download the verification package](https://github.com/ManuelManas/btp-pbf-verification/releases/latest/download/BTP_PBF_Verification.zip)** · [SHA-256 checksum](https://github.com/ManuelManas/btp-pbf-verification/releases/latest/download/BTP_PBF_Verification.zip.sha256)

The [correspondence table](verification/LEAN_CORRESPONDENCE.txt) identifies each formalized manuscript result, its hypotheses and its Lean declaration. It covers the semi-infinite existence criterion, Toeplitz factorization and the bounded and relative stability criteria. The spectral chapter is supported by [computational checks](computations/RECORDED_CHECKS.json). The [scope of verification](verification/VERIFICATION_SCOPE.json) gives the precise coverage.

## Lean audit

Lean compiled all 188 listed modules in four independent projects. The [audit report](verification/lean_audit/RESULTS.json) records 5,346 transitive axiom checks, counting shared declarations separately in each project. The axioms observed were `propext`, `Classical.choice` and `Quot.sound`.

| Project | Modules | Theorem checks |
| --- | ---: | ---: |
| [Semi-infinite factorizations](lean/semi_infinite) | 29 | 929 |
| [Toeplitz factorizations](lean/toeplitz) | 42 | 1,265 |
| [Scalar stability](lean/stability) | 3 | 110 |
| [General stability](lean/general_stability) | 114 | 3,042 |

## Reproduction

To compile the general stability proofs and run their axiom audit, use the following commands.

```sh
cd lean/general_stability
lake build
```

The Lake target runs `python3 bootstrap.py` followed by `sh check.sh`. You can also run those commands directly from the same directory. Both methods rebuild every module and run the same axiom audit. The dependency download now retries transient network errors and verifies each archive against its pinned SHA-256 checksum.

On a fresh Ubuntu arm64 system with an empty Mathlib cache, `lake build` verified 3,143 dependency archives, compiled all 114 general stability modules and passed the axiom audit for 3,042 theorem declarations. See the [Ubuntu build log](verification/lean_audit/general_stability_ubuntu.log).

The [instructions](README.txt) list the pinned toolchain, dependency checks, build commands and commands for reproducing the computational results. The [manifest](MANIFEST.json) lists the SHA-256 hashes of the files supplied in the download.
