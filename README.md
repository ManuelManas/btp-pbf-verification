# BTP/PBF: formal proofs and exact computational checks

Companion verification code for **Banded Totally Positive Matrices and
Positive Bidiagonal Factorizations: Existence, Stability, and Toeplitz
Orthogonality**, by Manuel Mañas.

The [correspondence table](verification/LEAN_CORRESPONDENCE.txt) identifies
the manuscript results, their numbers and printed pages in both editions,
the Lean declarations and their exact hypotheses. The result numbers and page references were checked
against the compiled manuscripts on 25 October 2026. Stable LaTeX labels and
Lean declaration names identify the results independently of their numbering;
old numbers retained in declaration names are code identifiers. No particular
arXiv upload is asserted.

This release updates the correspondence and descriptions. The Lean sources,
computational scripts and recorded outputs are unchanged from the
[general-stability release of 19 October 2026](https://github.com/ManuelManas/btp-pbf-verification/releases/tag/2026-10-19-general-stability).
Its build and axiom-audit records are retained with their original scope;
no new formal build or axiom audit was run for this documentation update.

## Formal coverage

| Project | Proved content |
| --- | --- |
| [Semi-infinite](lean/semi_infinite) | Finite row construction, extraction recurrences, inverse-minor identities and bounds, global criteria from compatible Metelmann factors. The candidate two-sided factorization may have an arbitrary positive diagonal; its normalization is proved explicitly. |
| [Toeplitz](lean/toeplitz) | BTP if and only if PBF, with positive bounded factors, without a root-criterion assumption. The complete characterization involving TN and negative roots is separately conditional on the explicitly named classical input `EdreiPolynomialInput`. |
| [Scalar stability and radius](lean/stability) | The complete weighted-shift lemma in real ℓ∞, including its inverse norm and one-block criterion; the exact scalar periodic reduction; and the abstract quantitative contraction argument, its combinatorial constants and positivity estimates. |
| [General stability](lean/general_stability) | Complete fixed-data, variable-data and arbitrary-growth relative criteria; normalized LDU, local inverses, global fixed-data uniqueness, and the actual bounded operator-norm realization. |

## General stability theorems

The [general-stability project](lean/general_stability) proves the actual
analytic factorization criteria in arbitrary finite bandwidth:

- Fixed initial entries: the lower and full-band equivalences.
- Variable initial entries: all pair conditions, with either geometric
  direction for each pair; the full-band criterion also uses the actual
  joint signed-inverse row sums.
- Relative errors: the triangular and full-band equivalences for arbitrary
  positive growth, without absolute bounds on the factors or the diagonal.
- Analytic normalized LDU, local inverse and Lipschitz conclusions.
- The actual realization as bounded operators on real ℓ² and the comparison
  of coefficient norm with operator norm, including transport of the bounded
  full-band criteria to operator-norm neighborhoods.

The matrix multiplication maps, their derivatives and all necessary inverse
estimates are proved. The final criteria do not assume the inverse or analytic
choice they conclude. The [correspondence table](verification/LEAN_CORRESPONDENCE.txt)
records exact statements, hypotheses and current numbers.

This does not formalize every result in the stability chapter. In particular,
interiority, the dimension of local families, the realization of unbounded
closed operators and the spectral theory are not claimed. The relative theorem
uses entrywise relative errors, not Kato perturbations. The earlier quantitative
radius module retains its explicitly documented partial scope. Finite scripts
are computational checks, not proofs of infinite-dimensional statements.

## Reproduce the proofs and axiom audit

The toolchain is pinned to Lean `leanprover/lean4:v4.34.0-rc2` and Mathlib
commit `85e3a25e006c35636f0e53b0e9296caca2685bc0`.
Install the toolchain with [elan](https://github.com/leanprover/elan), then run:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
cd lean/semi_infinite
python3 bootstrap.py
sh check.sh
cd ../toeplitz
python3 bootstrap.py
sh check.sh
cd ../stability
python3 bootstrap.py
sh check.sh
cd ../general_stability
python3 bootstrap.py
sh check.sh
```

Each `check.sh` starts with an empty directory of local compiled modules,
treats warnings as errors, and audits the transitive axiom dependencies of
**every project theorem**, including generated auxiliary proofs. It fails
on an axiom outside `propext`, `Classical.choice`, and `Quot.sound`.
These are Lean's standard foundational axioms, not additional mathematical
assumptions. Explicit theorem hypotheses must still be inspected; in particular,
the axiom audit does not prove `EdreiPolynomialInput`.

The general-stability project contains 114 mathematical source modules,
including its required legacy sources, plus the `AxiomAudit.lean` utility.
It audits 3042 theorem constants with their dependencies. These include auxiliary declarations and
are not counts of new manuscript results. Earlier projects retain their recorded
builds. The [build records](verification/build_records/general_stability) include
the compilation and independent semantic reviews recorded on 19 October 2026. Across the four active
projects there are 188 mathematical source modules and four
`AxiomAudit.lean` utilities; shared sources are counted in each project.

The dependency bootstrap verifies 3143 pinned cache archives
and compiles one checksum-verified source module from the same Mathlib commit.
This is not a source rebuild of all Mathlib. Use `bootstrap.py --offline` with
an existing archive cache. `BTP_LEAN_BIN` and `BTP_LEANTAR` support nonstandard
toolchain locations.

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


Additional historical scripts and their recorded scope are described in
[verification/README.md](verification/README.md). They have not been rerun
or promoted to formal proofs by this documentation update.

## Citation and archived records

The [current verification release](https://github.com/ManuelManas/btp-pbf-verification/releases/tag/2026-10-25-correspondence) contains sources, correspondence,
instructions and build records. Citation metadata are in [CITATION.cff](CITATION.cff).
Earlier releases and their original correspondence tables remain available for reproducibility. Legacy names in
`verification_v64` and old declaration identifiers are historical records,
not the identifier or claimed coverage of this verification package.
No Zenodo deposit or DOI is claimed by this update.
