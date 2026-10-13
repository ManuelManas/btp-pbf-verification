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
current release accompanies **manuscript v64, 13 October 2026**;
[v48](https://github.com/ManuelManas/btp-pbf-verification/tree/v48) preserves the initial release.

## Contents

| Directory | Contents |
| --- | --- |
| [`lean/semi_infinite`](lean/semi_infinite) | Finite row reconstruction, inverse-minor identities and bounds, the determinant extraction identity, and the criterion involving the **p + q − 2 positive limits**, starting from compatible Metelmann factors. |
| [`lean/toeplitz`](lean/toeplitz) | The direct Toeplitz implication **BTP ⇒ PBF**, its converse, and uniform bounds on the positive factors. |
| [`computational`](computational) | Exact checks with rational and symbolic arithmetic, and multiprecision checks of density moments; scripts and recorded outputs. |

The two Lean projects contain 70 source files in total, including shared
modules. Each project has a `modules.txt` file specifying the compilation order.
The detailed correspondence with the manuscript, including index shifts, is in
[`LEAN_CORRESPONDENCE_v64.txt`](verification_v64/LEAN_CORRESPONDENCE_v64.txt) and summarized below.

| Result | Lean source |
| --- | --- |
| Reconstruction one row at a time | [`Lemma24.lean`](lean/semi_infinite/Lemma24.lean) |
| Successive factor-extraction recurrences | [`Proposition29.lean`](lean/semi_infinite/Proposition29.lean) |
| Bounds from inverse entries | [`Proposition215.lean`](lean/semi_infinite/Proposition215.lean) |
| Inverse minors and their uniform bounds | [`InverseMinors.lean`](lean/semi_infinite/InverseMinors.lean), [`SharpUniformMinors.lean`](lean/semi_infinite/SharpUniformMinors.lean), [`CompleteSharpResults.lean`](lean/semi_infinite/CompleteSharpResults.lean) |
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

## Exact uniform constant added in v64

The manuscript uses the maximum of 1 and all consecutive products of the
adjacent Metelmann series. `SharpUniformMinors.lean` proves the estimate
with precisely this constant, following the manuscript: bound each nested
sum, take the finite maximum, and expand the normalized determinant.
`CompleteSharpResults.lean` also states the raw minor identity, its zero-row
case and strict positivity at positive row indices.

The original 68 Lean sources from v48 are retained unchanged. Their larger
uniform bound already suffices for the global existence theorem. Version
v64 adds two modules establishing the manuscript's literal, sharper bound.

All **28 modules** of the semi-infinite project were checked in an empty
local build directory with warnings treated as errors. The new theorems and
the global criterion report only `propext`, `Classical.choice` and
`Quot.sound`. See the [compilation log](verification_v64/lean_clean_build.log)
and [validation record](verification_v64/validation.json). The Toeplitz
project is unchanged from v48.

The additional [v63 computational checks](computational/audit_v63) include
the supplied Section 2 and Section 3 scripts and the exact tail-certificate
script, with their recorded outputs and pinned Python dependencies.

## Version and citation

Use the immutable tag
[`v64`](https://github.com/ManuelManas/btp-pbf-verification/tree/v64)
or its commit hash when citing this revision. Citation metadata are in
[`CITATION.cff`](CITATION.cff).

[`SHA256SUMS_v64.txt`](SHA256SUMS_v64.txt) records the sources and documentation
in this release. `SHA256SUMS.txt` is retained as the original v48 manifest.
