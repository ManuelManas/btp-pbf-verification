# BTP/PBF: formal proofs and exact computational checks

Companion verification code for **Banded Totally Positive Matrices and
Positive Bidiagonal Factorizations: Existence, Stability, and Toeplitz
Orthogonality**, by Manuel Mañas.

Verification archive: **dichotomies and ordered root partitions, 17 October 2026**.
See [verification](verification/README.md) for the computational checks,
the [correspondence table](verification/LEAN_CORRESPONDENCE.txt),
and [scope](verification/VERIFICATION_SCOPE.json).
The formal sources and their build records are preserved unchanged.
The new stability and spectral results have written proofs and
computational checks; they are not formalized in Lean.

## Contents

| Directory | Contents |
| --- | --- |
| [`lean/semi_infinite`](lean/semi_infinite) | Finite row reconstruction, inverse-minor identities and bounds, the determinant extraction identity, and the criterion involving the **p + q − 2 positive limits**, starting from compatible Metelmann factors. |
| [`lean/toeplitz`](lean/toeplitz) | The direct Toeplitz implication **BTP ⇒ PBF**, its converse, and uniform bounds on the positive factors. |
| [`computational`](computational) | Exact checks with rational and symbolic arithmetic, and multiprecision checks of density moments; scripts and recorded outputs. |

The two Lean projects contain 70 source files in total, including shared
modules. Each project has a `modules.txt` file specifying the compilation order.
The detailed correspondence with the manuscript, including index shifts, is in
[`LEAN_CORRESPONDENCE.txt`](verification/LEAN_CORRESPONDENCE.txt) and summarized below.

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
for comparison. The recorded results show that all four scripts completed successfully.
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

## Exact uniform-minor constant

`SharpUniformMinors.lean` proves the displayed manuscript bound using the
maximum of 1 and all consecutive products of adjacent Metelmann series.
`CompleteSharpResults.lean` records the raw minor identity, the zero-row
case, strict positivity, and the sharp bound.

The recorded clean build checks all 28 semi-infinite modules with warnings
treated as errors. The reported foundational axioms are `propext`,
`Classical.choice`, and `Quot.sound`. See the preserved
[build log](verification/build_records/lean_clean_build.log) and
[validation record](verification/build_records/validation.json).
These records describe the earlier formal build; the present update does
not claim a fresh Lean build or formal proofs of the stability and spectral
results. The source hashes in the correspondence table identify the exact
formal files used.

## Citation

The [dated verification archive](https://github.com/ManuelManas/btp-pbf-verification/releases/tag/2026-10-17-dichotomies)
contains the sources, correspondence table, checks and hashes.
Citation metadata are in [`CITATION.cff`](CITATION.cff).
