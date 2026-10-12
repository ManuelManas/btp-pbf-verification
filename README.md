# BTP/PBF: formal proofs and exact computational checks

Companion verification code for **Positive Bidiagonal Factorizations and
Mixed-Type Chebyshev Multiple Orthogonal Polynomials**, by Manuel Mañas.

A positive bidiagonal factorization (PBF) expresses a banded matrix as an
ordered product of lower bidiagonal factors, a positive diagonal factor,
and upper bidiagonal factors, with positive entries in the allowed positions.
The manuscript studies when a banded totally positive (BTP) matrix admits
such a factorization and uses Toeplitz factorizations to construct polynomial
families and their orthogonality measures.

This repository contains Lean proofs for selected factorization results and
Python scripts for exact checks of finite examples and identities. The
initial release accompanies **manuscript v48, 12 October 2026**.

## Contents

| Directory | Contents |
| --- | --- |
| [`lean/semi_infinite`](lean/semi_infinite) | Finite row reconstruction, inverse-minor identities and bounds, the determinant extraction identity, and the criterion involving the **p + q − 2 positive limits**, starting from compatible Metelmann factors. |
| [`lean/toeplitz`](lean/toeplitz) | The direct Toeplitz implication **BTP ⇒ PBF**, its converse, and uniform bounds on the positive factors. |
| [`computational`](computational) | Four exact computational checks, using rational arithmetic or symbolic polynomial identities. |

The two Lean projects contain 68 source files in total, including shared
modules. Each project has a `modules.txt` file specifying the compilation order.
The correspondence with the manuscript is listed in
[`README.txt`](README.txt) and summarized below.

| Result | Lean source |
| --- | --- |
| Reconstruction one row at a time | [`Lemma24.lean`](lean/semi_infinite/Lemma24.lean) |
| Successive factor-extraction recurrences | [`Proposition29.lean`](lean/semi_infinite/Proposition29.lean) |
| Bounds from inverse entries | [`Proposition215.lean`](lean/semi_infinite/Proposition215.lean) |
| Inverse minors and their uniform bounds | [`InverseMinors.lean`](lean/semi_infinite/InverseMinors.lean), [`UniformMinors.lean`](lean/semi_infinite/UniformMinors.lean) |
| Extraction determinant identity, including vanishing recurrence terms | [`UnrestrictedDeterminant.lean`](lean/semi_infinite/UnrestrictedDeterminant.lean) |
| Global criterion for both bandwidths | [`CompleteResults.lean`](lean/semi_infinite/CompleteResults.lean) |
| Toeplitz BTP ⇔ PBF | [`BTPToPBF.lean`](lean/toeplitz/BTPToPBF.lean) |

The Lean theorem statements record their hypotheses explicitly. The separate
files concerning total nonnegativity and negative roots retain their named
classical hypotheses. The direct BTP ⇒ PBF result is in `BTPToPBF.lean`.
The polynomial and measure formulas are treated in the manuscript; the Lean
sources supplied here concern the factorization results listed above.

## Run the exact computational checks

The first two scripts use Python 3 and its standard library:

```sh
python3 computational/geometric_coefficients.py
python3 computational/constant_factor_orders.py
```

The other two use SymPy, with version 1.13.2 used for the supplied results.
For example, create a virtual environment and run:

```sh
python3 -m venv .venv
. .venv/bin/activate
python -m pip install -r requirements.txt
python computational/finite_parameter_example.py
python computational/finite_parameter_domain.py
```

| Script | What it checks |
| --- | --- |
| `geometric_coefficients.py` | Coefficient identities for geometric root parameters, their binomial specialization, and affine-comparison invariants. |
| `constant_factor_orders.py` | Products of constant bidiagonal factors under stable interleavings, their Toeplitz symbols, and the support, rank, and sign of the boundary correction. |
| `finite_parameter_example.py` | Exact symbolic factorization formulas and polynomial inequalities in the five-dimensional example. |
| `finite_parameter_domain.py` | The description of the admissible three-parameter domain and its boundary faces. |

Each script writes a JSON report beside its source. These reports are included
for comparison. All four scripts completed successfully for the v48 supplement.
They check the finite cases and identities specified in their source files.

## Check the Lean proofs

The projects pin the following versions:

- **Lean:** `leanprover/lean4:v4.34.0-rc2`
- **mathlib:** commit `85e3a25e006c35636f0e53b0e9296caca2685bc0`

Install that Lean toolchain using [elan](https://github.com/leanprover/elan),
then run each project from its own directory:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2

cd lean/semi_infinite
python3 bootstrap.py
sh check.sh

cd ../toeplitz
python3 bootstrap.py
sh check.sh
```

`bootstrap.py` obtains the pinned dependency archives and verifies their
SHA-256 hashes. `check.sh` compiles the modules in a fresh output directory
with warnings treated as errors. The source files include `#print axioms`
commands for the main results.

For an existing dependency cache, use `python3 bootstrap.py --offline`.
The variables `BTP_LEAN_BIN` and `BTP_LEANTAR` allow matching executables
installed outside the standard elan directory.

The Lean sources in this release are unchanged from the verification
packages assembled during the development of the manuscript.

## Version and citation

The tag [`v48`](https://github.com/ManuelManas/btp-pbf-verification/tree/v48)
records the code accompanying manuscript v48. Use that tag or its commit hash
when citing a particular version. Citation metadata are provided in
[`CITATION.cff`](CITATION.cff).

[`SHA256SUMS.txt`](SHA256SUMS.txt) records the files in the original v48
verification supplement. The repository adds this README, citation metadata,
dependency instructions, and Git configuration files; its Lean and
computational sources have the same contents as the supplement.
