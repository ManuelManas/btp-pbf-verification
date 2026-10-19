# Scope of WeightedShift.lean

## Manuscript correspondence

The stable reference is the LaTeX label `stab:lem:weighted-shift`,
“Bounded inverse and products over blocks”, and its displayed row-sum
formula `stab:eq:shift-row-sum`. References use labels rather than a
particular manuscript version or theorem number.

This module proves the full scalar weighted-shift lemma on the real
Banach space of bounded sequences, including its explicit inverse norm
estimate and its equivalent one-block formulation. It also proves the
row-sum equivalence used in the relative, possibly unbounded theory.
It does **not** formalize the matrix PBF stability theorems, the
matrix derivative factorization, the pairwise dichotomy necessity,
or an analytic inverse-function theorem for the multiplication map.
Those results cannot be marked as formalized merely because this
scalar lemma is formalized.

## Objects and indexing

* `BoundedSequence` is `BoundedContinuousFunction ℕ ℝ`, with the usual
  supremum norm. Since the natural numbers have the discrete topology,
  these are precisely all bounded real sequences; `ofAbsBound`
  constructs such an object from any uniform absolute bound.
* Row zero is the initial row. Given the manuscript's initial row
  `n₀`, reindex by setting `w k = γ(n₀+k)` for `k ≥ 1`; `w 0` is unused
  and may be set to zero. The forcing and solution are reindexed in
  the same way.
* `blockProduct w s N` is the product of `w(s+1), …, w(s+N)`.
  Thus it is the manuscript's product starting at `n=n₀+s+1`.
* `rowSum w n` is first defined by the recurrence `z₀=1`,
  `zₙ₊₁=1+w(n+1)zₙ`. The theorem `rowSum_eq_sum` proves, rather than
  assumes, that it equals the sum of the Green coefficients in row n.
* `differenceMap w` has initial entry `(Dv)₀=v₀` and later entries
  `(Dv)ₙ₊₁=vₙ₊₁−w(n+1)vₙ`. Thus it is exactly `I−W`, including the
  initial equation. Its linearity and boundedness are proved.
* The input weights are only assumed nonnegative. This is slightly
  stronger than the manuscript, which assumes strictly positive
  weights. It introduces no additional mathematical assumption.
* Geometric estimates include `N=0` for convenience. The added case
  is automatic from `C ≥ 1`, since the empty product is one.

## Main declarations

1. `rowSum_eq_sum`: explicit finite Green row-sum formula.
2. `rowSum_bounded_iff_geometric`: a uniform row-sum bound is equivalent
   to a uniform geometric bound for every consecutive product. No
   prior bound on the weight sequence is assumed here. The proof of
   necessity uses the positive recurrence itself and a telescoping
   estimate, not a hypothesis equivalent to the conclusion.
3. `forwardSolution_unique`: the recurrence has exactly the stated
   forward solution, without assuming boundedness.
4. `forwardSolution_bound`: the pointwise solution estimate for
   uniformly bounded forcing.
5. `differenceMap_bijective_iff_geometric`: on real l-infinity, `I−W`
   is a bounded bijection exactly when the products decay uniformly
   geometrically. The forward implication applies surjectivity to the
   constant-one sequence and then proves the row-sum bound. The reverse
   implication constructs a bounded solution for every bounded datum.
6. `differenceEquiv`: the continuous linear inverse is constructed
   explicitly from forward substitution; both inverse identities are
   proved, not assumed.
7. `weighted_shift_inverse_norm_bound`: under a geometric bound with
   constants C and rho, the constructed inverse satisfies
   `norm((I−W)⁻¹) ≤ 1+C*rho/(1−rho)`, exactly as in the manuscript.
8. `geometric_iff_block_contraction`: for uniformly bounded
   nonnegative weights, geometric decay is equivalent to existence of
   a positive block length h and theta in `[0,1)` bounding every
   length-h product. The use of `[0,1)` rather than `(0,1)` admits zero
   weights; increasing theta to `(1+theta)/2` gives the manuscript's
   strictly positive theta if desired.

## Axiom and compilation check

Run from the verification project:

```
./run_lean.sh -DwarningAsError=true -o .build/WeightedShift.olean WeightedShift.lean
```

`WeightedShift.check.log` records a successful compilation with warnings
as errors and explicit `#print axioms` output for the main exports.
Their dependencies are only Lean's standard logical foundations:
`propext`, `Classical.choice`, and `Quot.sound`. There are no custom
axioms, `sorry`, `admit`, or `sorryAx` dependencies in the theorem proofs.

The mathematical content is infinite-dimensional: the estimates and
bijection quantify over all natural-number rows and all bounded real
sequences. They are not finite-section numerical tests.
