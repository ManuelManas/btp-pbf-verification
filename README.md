# BTP/PBF: formal proofs and exact computational checks

Companion verification code for **Banded Totally Positive Matrices and
Positive Bidiagonal Factorizations: Existence, Stability, and Toeplitz
Orthogonality**, by Manuel Mañas.

The [correspondence table](verification/LEAN_CORRESPONDENCE.txt) identifies
the manuscript results, their current numbers in both editions, the Lean
declarations and their exact hypotheses. It uses stable mathematical labels;
it is not tied to a manuscript version number or to the preliminary arXiv upload.

## Formal coverage

| Project | Proved content |
| --- | --- |
| [Semi-infinite](lean/semi_infinite) | Finite row construction, extraction recurrences, inverse-minor identities and bounds, global criteria from compatible Metelmann factors. The candidate two-sided factorization may have an arbitrary positive diagonal; its normalization is now proved explicitly. |
| [Toeplitz](lean/toeplitz) | BTP if and only if PBF, with positive bounded factors, without a root-criterion assumption. The complete characterization involving TN and negative roots is separately conditional on the explicitly named classical input `EdreiPolynomialInput`. |
| [Stability](lean/stability) | The complete weighted-shift lemma in real ℓ∞, including its inverse norm and one-block criterion; the exact scalar periodic reduction; and the abstract quantitative contraction argument, its combinatorial constants and positivity estimates. |

**The whole stability chapter is not formalized.** The abstract radius result
takes a bounded linear inverse and remainder estimates as inputs. Its general
realization for band-matrix multiplication and the analytic PBF criteria remain
written proofs. The Jacobi-fraction reformulation and polynomial/spectral/measure
theory are also outside Lean coverage. The computational scripts test the
specified finite cases; they do not prove those infinite-dimensional theorems.

## New formal proofs

- [WeightedShift.lean](lean/stability/WeightedShift.lean): the actual continuous
  linear operator I−W on bounded sequences is bijective exactly when products
  of its nonnegative weights decay uniformly geometrically. An explicit inverse
  has norm at most 1+Cρ/(1−ρ). A single uniformly contractive block is equivalent
  to this condition for bounded weights. The row-sum equivalence does not require
  an a priori bound on the weights.
- [PeriodicStability.lean](lean/stability/PeriodicStability.lean): the preceding
  decay condition is equivalent to a period product less than one. For shifted
  adjacent factor ratios this is exactly strict ordering of period products.
- [AnalyticRadius.lean](lean/stability/AnalyticRadius.lean): under the displayed
  linear-inverse and remainder estimates, there is a unique solution in the
  variation ball, with image bound 3r/4 and Lipschitz constant 2M. The exact
  arbitrary-bandwidth combinatorial bounds and positivity estimate are proved;
  the product expansion is also checked for two factors in any normed ring.
- [ArbitraryDiagonalBridge.lean](lean/semi_infinite/ArbitraryDiagonalBridge.lean):
  uniqueness of the normalized diagonal from leading-section determinants,
  followed by the two-sided inverse-minor criterion with an arbitrary candidate
  positive diagonal.

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
```

Each `check.sh` starts with an empty directory of local compiled modules,
treats warnings as errors, and audits the transitive axiom dependencies of
**every project theorem**, including generated auxiliary proofs. It fails
on an axiom outside `propext`, `Classical.choice`, and `Quot.sound`.
These are Lean's standard foundational axioms, not additional mathematical
assumptions. Explicit theorem hypotheses must still be inspected; in particular,
the axiom audit does not prove `EdreiPolynomialInput`.

The current clean build covers 29 semi-infinite, 42 Toeplitz and 3 stability
modules. Shared sources are counted separately in the first two projects;
these are not counts of distinct manuscript results. Three additional
`AxiomAudit.lean` files provide the audit utilities.
The [build records](verification/build_records) include independent semantic
reviews, fresh compilation logs and the verified dependency bootstrap.
The 3095 pinned dependency archives were checked and unpacked into a new
directory. This reproduces the cached Mathlib artifacts, not a source build
of Mathlib itself. Use `bootstrap.py --offline` for an existing archive cache.
`BTP_LEAN_BIN` and `BTP_LEANTAR` support nonstandard toolchain locations.

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
or promoted to formal proofs by the present Lean update.

## Citation and archived records

The [verification release](https://github.com/ManuelManas/btp-pbf-verification/releases/tag/2026-10-19-stability) contains sources, correspondence,
instructions and build records. Citation metadata are in [CITATION.cff](CITATION.cff).
Earlier releases remain available for reproducibility. Legacy names in
`verification_v64` and old declaration identifiers are historical records,
not the identifier or claimed coverage of this verification package.
No Zenodo deposit or DOI is claimed by this update.
