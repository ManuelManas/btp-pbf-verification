# Quantitative perturbation radius: verified scope

Correspondence: manuscript label `stab:rem:general-radius` (the proposition
entitled **A quantitative perturbation radius**). The statement is tracked by
its LaTeX label and title, not by an internal manuscript version or page number.

`AnalyticRadius.lean` verifies the following parts of its proof.

1. For arbitrary real normed spaces of variations and data, with the variation
   space complete, a continuous linear equivalence `D`, inverse bound `M`,
   quadratic remainder bound `C r²`, and remainder Lipschitz bound `2 C r`,
   the inequalities `M C r ≤ 1/4` and `‖e‖ ≤ r/(2M)` imply existence and
   uniqueness of a solution to `D h + R h = e` in `‖h‖ ≤ r`.
2. The solution in fact satisfies `‖h‖ ≤ 3r/4`.
3. Two solutions in that ball satisfy
   `‖h-k‖ ≤ 2M ‖e-f‖`.
4. The manuscript's radius bound `r ≤ 1/(4MC)` implies the smallness condition
   used in this argument when `M,C > 0`.
5. If every original entry is at least `α`, and the uniform entry variation is
   at most `r ≤ α/2`, every perturbed entry is at least `α/2`. This theorem
   allows an arbitrary, possibly infinite, index type.
6. For every number of factors `p=d+2`, both binomial comparisons and both
   sums used to bound the quadratic remainder and its Lipschitz constant are
   proved. The exact constant is
   `C_p = p(p-1)(2+A)^(p-2)/2`.
7. For two factors in an arbitrary (possibly noncommutative) normed ring, the
   product expansion and the actual quadratic remainder bounds are proved
   without assuming these bounds. This applies in particular to bounded
   operators, once their space and the derivative are supplied.

## Explicit boundary of the formalization

The general Banach-space theorem assumes the continuous linear equivalence
and the two remainder estimates. They are printed hypotheses, not axioms.
The file does **not** construct the inverse derivative from the adjacent
factor conditions, formalize the banded operator spaces and prescribed-entry
subspaces, identify the full product remainder for arbitrary bandwidth, or
prove real analytic dependence. The arbitrary-bandwidth **scalar binomial
majorants** are formalized, but their assembly with the operator-product
expansion and the previously established factorization criterion still
belongs to the written proof.

The existence/uniqueness argument is a use of mathlib's Banach contraction
theorem, on the complete closed ball. No application-specific axiom,
`sorry`, `admit`, or `sorryAx` is used. The checked exported theorems depend
only on Lean's standard `propext`, `Classical.choice`, and `Quot.sound`.

## Principal declarations

- `PBFStability.quantitative_radius`
- `PBFStability.quantitative_radius_lipschitz`
- `PBFStability.quantitative_radius_solution_bound`
- `PBFStability.radius_small_of_bound`
- `PBFStability.positive_entries_of_radius`
- `PBFStability.remainderConstant_eq`
- `PBFStability.quadratic_majorant_bound`
- `PBFStability.lipschitz_majorant_bound`
- `PBFStability.twoFactor_expansion`
- `PBFStability.twoFactor_remainder_bound`
- `PBFStability.twoFactor_remainder_lipschitz`

The Lean source includes `#print axioms` commands for the principal results;
the strict compiler command uses `-DwarningAsError=true`.
