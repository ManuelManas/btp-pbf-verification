import PositiveLimits
import OneFactorFormula

/-! # Public statement of the formalized sufficient criterion

Input: compatible Metelmann data on both sides and a positive diagonal.
Conclusion: one global PBF, assuming the p+q-2 ACTUAL inverse-minor limits
are strictly positive. The supplied factor arrays may be unbounded.
-/
open Matrix Finset Filter
open scoped Topology
noncomputable section
namespace BTP.SemiInfinite

def twoSidedLimit (p q : ℕ) (a c : Entries) : ObstructionIndex p q → ℝ
  | Sum.inl k => inverseMinorLimit a p k.val
  | Sum.inr k => inverseMinorLimit c q k.val

/-- There are exactly p+q-2 coordinates, including the empty p=q=1 case. -/
theorem p_add_q_sub_two_positive_limits {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {a c : Entries} {D : ℕ → ℝ}
    (ha : Metelmann p a) (hc : Metelmann q c) (hD : ∀ n, 0 < D n)
    (hlimits : ∀ i : ObstructionIndex p q, 0 < twoSidedLimit p q a c i) :
    HasTwoSidedPBF p q a c D ∧ Fintype.card (ObstructionIndex p q) = p + q - 2 := by
  refine ⟨positive_limits_give_two_sided_PBF hp hq ha hc hD ?_ ?_, number_of_limits hp hq⟩
  · intro k hk
    exact hlimits (Sum.inl ⟨k, by omega⟩)
  · intro k hk
    exact hlimits (Sum.inr ⟨k, by omega⟩)

/-- The infimum used in the statement is indeed the sequential limit. -/
theorem inverse_minor_limit_is_limit {p k : ℕ} {a : Entries}
    (ha : Metelmann p a) (hk : k + 1 < p) :
    Tendsto (inverseMinorRatio a p k) atTop (𝓝 (inverseMinorLimit a p k)) := by
  rw [inverseMinorLimit_eq_seriesEndpoint ha hk]
  exact inverseMinorRatio_tendsto ha hk

/-- Positive arrays in the conclusion give actual positive bidiagonal matrices
in every finite leading section, rather than only a name for an abstract property. -/
theorem positive_factors_are_matrices {p : ℕ} {b : Entries} (hb : Positive p b)
    (d j : ℕ) (hj : j < p) : PositiveLowerBidiagonal (bidiagonal d (b j)) := by
  refine ⟨bidiagonal_unit d (b j), ?_⟩
  intro i k hik
  rw [bidiagonal_subdiagonal _ _ _ hik]
  exact hb j hj i.val (by omega)

#print axioms p_add_q_sub_two_positive_limits
#print axioms inverse_minor_limit_is_limit
#print axioms extraction_recurrence_positive
#print axioms extraction_determinant_formula
#print axioms uniform_inverse_minors
#print axioms all_small_parameters_extend
#print axioms global_first_limit_positive
end BTP.SemiInfinite
