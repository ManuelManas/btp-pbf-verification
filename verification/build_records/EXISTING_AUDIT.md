# Independent audit of the existing Lean formalization

Audit date: 19 October 2026. This report audits the existing public sources and adds one explicit normalization bridge. It does not claim that the new stability chapter, the spectral theory, or the entire manuscript has been formalized.

## Inputs and method

- Public source checkout: `staging/btp-pbf-public-v86`, commit `9576e4f` (unchanged by this audit).
- Manuscript compared: the author's current Normal snapshot in `working/btp_lean_stability_v117/source/BTP_PBF_Normal_2026-10-19_v116.tex`.
- Lean: `leanprover/lean4:v4.34.0-rc2`.
- Mathlib: commit `85e3a25e006c35636f0e53b0e9296caca2685bc0`.
- All 28 modules in the semi-infinite project and all 42 modules in the Toeplitz project were rebuilt into new, initially empty local compilation directories. These counts include the common modules repeated in both projects; they are not 70 distinct mathematical results.
- Compilation used `-DwarningAsError=true`. Both runs completed successfully.
- An environment-level audit imported every module listed in each `modules.txt`, enumerated every theorem whose name belongs to the project's `BTP` namespaces (including private and generated auxiliary proofs), and inspected its complete axiom dependency list.
- All 924 theorem constants in the semi-infinite environment and all 1265 theorem constants in the Toeplitz environment depend only on a subset of `propext`, `Classical.choice`, and `Quot.sound`. These are Lean's standard foundational axioms, not manuscript assumptions. There is no dependency on `sorryAx` or a project-specific axiom.
- A source scan found no `sorry`, `admit`, custom axiom declaration, `unsafe`, `implemented_by`, or `native_decide` in the 70 original files. The word `axiom` occurs only in a comment explaining the explicit classical root hypothesis.

Successful build logs: `semi_infinite_clean_build.log`, `toeplitz_clean_build.log`.
Axiom audit sources: `semi_infinite/AxiomAudit.lean`, `toeplitz/AxiomAudit.lean`.
Axiom audit logs: `semi_infinite_axioms.log`, `toeplitz_axioms.log`.

## Meaning of the formal statements

The manuscript statements and the key definitions used by their Lean representations were compared directly, including hypotheses, quantifiers, indexing, matrix products and positivity conventions. This semantic check is distinct from compilation. Compilation checks the Lean proof of its Lean statement; it cannot itself verify the translation from the paper.

| Manuscript label | Scope verified |
| --- | --- |
| `lem:rowwise` | The finite row-by-row refactorization takes the Metelmann zero pattern and positive remaining entries as input. It constructs actual finite bidiagonal matrices, keeps the product unchanged, gives analytic dependence near zero, and proves positivity for all sufficiently small positive free parameters. The count `p(p-1)/2` is formalized. |
| `prop:successive-recurrences` | The recurrence characterization includes its forward and converse implications, nonzero initial data and nonvanishing recurrence hypotheses, actual factorization and inverse identities, and the final bandwidth-one factor. Positivity/nonvanishing of a desired output is not silently assumed in the positive iteration argument. |
| `prop:inverse-parameter-bound` | Signed entries of the actual finite inverse are positive, the ratios strictly decrease, and the strict first-entry bound applies to arbitrary positive matrix factors through a separate coordinate-representation theorem. |
| `lem:global-inverse-minors` | The leading-minor identity and positivity cover every order up to `p` and row zero. The next-minor formula includes its zero-row value, strict positivity begins at manuscript row one, and the ratio is strictly decreasing with the correct limit. The sharp uniform constant is the exact displayed maximum, giving `k! B^k`, not the older weaker bound. |
| `lem:global-extraction-determinant` | The determinant identity has no nonvanishing assumption on the later recurrence terms; the unrestricted declaration even allows arbitrary initial values. Positive extraction follows separately from positive determinants and the stated positive initial/extreme entries. `extraction_initial_determinant` supplies the automatic row-zero value one; the paper's hypothesis for rows `n >= 1` thus gives the all-rows premise used by `positive_extraction`. |
| `thm:global-lower-criterion` | Conditions (1), (2), (3), including sufficiently small positive initial data, are formalized for a compatible semi-infinite Metelmann product. `HasPBF` means one array of factors valid in every finite leading section (`exists factors, forall dimensions`), not a different factorization at each dimension. The Jacobi-fraction reformulation (4) is not formalized. |
| `cor:global-two-sided-criterion` | The positive inverse-minor limit criterion is formalized for supplied compatible lower/upper Metelmann factors and a positive normalized diagonal. An additional bridge described below removes an implicit common-diagonal restriction from the formal candidate PBF. The Jacobi-fraction identity and derivation of arbitrary BTP input data are not claimed here. |
| `thm:toeplitz` | The direct BTP-to-uniformly-positive-bounded-PBF construction and BTP iff PBF are proved without a negative-root or Edrei assumption. The proof constructs the required triangular Metelmann factors from positive minors, rather than assuming a PBF. Construction from supplied negative-root data is also proved. The full equivalence involving TN and negative roots remains conditional on the explicitly named `EdreiPolynomialInput`. |

### Index translation

The formal factors are numbered from zero on the right: `a j n` corresponds to the paper's `hat a_(p-j)(n)`. The formal inverse-minor order `k` denotes manuscript order `k+1`, and `inverseMinorRatio a p k n` denotes `kappa_(k+1,n+1)`. The leading-minor declarations cover order `p` separately even though the combined ratio wrapper uses `k+1 < p`. All-zero / empty-list boundary cases are handled explicitly.

### The explicit classical root input

`EdreiPolynomialInput` is a proposition, defined as the classical implication from TN of the lower Toeplitz coefficient matrix to negative real roots. It is a parameter of `manuscript_theorem_3_2_given_Edrei`, not an axiom declaration and not a theorem proved in this project. An axiom list alone would not reveal this mathematical premise: the theorem signature and its definitions must be read. The correspondence must continue to distinguish this conditional full characterization from the unconditional BTP/PBF branch.

## Gap identified and closed: arbitrary diagonal in the two-sided criterion

The existing `HasTwoSidedPBF` definition uses the prescribed diagonal `D` in both the original and candidate factorization. Likewise, `normalized_products_unique` proves uniqueness of the two triangular products once the diagonals are already equal. In the manuscript, a candidate PBF may initially have its own positive diagonal, and the written proof invokes uniqueness of the entire normalized LDU decomposition.

This is a small missing formal bridge, not a false existing theorem. The new file `semi_infinite/ArbitraryDiagonalBridge.lean` closes it:

1. `triangularSections_det` proves that a leading-section determinant equals the finite product of the diagonal entries.
2. `normalized_diagonal_unique` compares products for dimensions `n` and `n+1`, cancelling the nonzero first product, and proves equality of the two diagonal sequences.
3. `HasArbitraryTwoSidedPBF` permits an arbitrary positive diagonal in the candidate factorization.
4. `arbitrary_two_sided_iff_normalized` and `arbitrary_two_sided_PBF_iff_positive_limits` prove the equivalence with the original normalized predicate and the inverse-minor limit criterion.

The new file compiled successfully with warnings treated as errors. Its printed axiom dependencies are only the three standard axioms above. See `normalization_bridge_build.log`. To integrate it, append `ArbitraryDiagonalBridge` to the semi-infinite module list and add the corresponding library target after `CompleteSharpResults`. No old source was modified during the audit.

## Dependency-cache reproduction

The existing cache manifest lists 3095 dependency archives. Every archive is present in the local shared cache and matches its recorded checksum; see `cache_audit.json`. The manifest includes all current direct Mathlib imports of the two new stability modules:

- `Mathlib.Analysis.SpecificLimits.Normed`
- `Mathlib.Topology.ContinuousMap.Bounded.Normed`
- `Mathlib.Analysis.Normed.Operator.Banach`
- `Mathlib.Topology.MetricSpace.Contracting`
- `Mathlib.Tactic`

The published `bootstrap.py --offline` was also exercised in a new directory with no existing `.deps`. It checksum-verified and unpacked all 3095 archives successfully, after which a probe importing all the new modules' Mathlib dependencies compiled. See `dependency_bootstrap.log` and `dependency_import_audit.log`. This verifies reproducibility from the pinned cached artifacts, not a rebuild of Mathlib itself from source.

## Commands

From each copied old project, `./check.sh` creates an empty local compilation directory and rebuilds its complete `modules.txt`. With that directory assigned to `BTP_BUILD_DIR`, run:

```sh
./run_lean.sh -DwarningAsError=true AxiomAudit.lean
./run_lean.sh -DwarningAsError=true -o "$BTP_BUILD_DIR/ArbitraryDiagonalBridge.olean" ArbitraryDiagonalBridge.lean
```

The second command applies only to the semi-infinite project. Cache reproduction, in `dependency_reproduction`, used the configured Python runtime with `bootstrap.py --offline`, followed by `./run_lean.sh -DwarningAsError=true ImportAudit.lean`.

## Limits of this audit

This audit confirms successful fresh compilation of the original local sources, their axiom dependencies, and the stated source-to-manuscript correspondence for the results above. It does not formally prove that the natural-language translation is correct, audit the entire Lean compiler or Mathlib implementation, or claim coverage of unformalized stability/spectral results. The new stability sources require their own compilation and semantic review before they are listed as formalized. Current manuscript numbers and pages should be regenerated from the new PDF auxiliary files; persistent LaTeX labels and Lean declaration names are the stable identifiers.
