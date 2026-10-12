import ExtractionDeterminants

open Matrix Finset
noncomputable section
namespace BTP.SemiInfinite
open Extraction InverseBounds

/-- Row recursion for the signed inverse of any unit lower triangular matrix. -/
def canonicalLowerInverse (F : NatMatrix) (n j : ℕ) : ℝ :=
  if n = j then 1 else if n < j then 0 else
    -(∑ k : Fin n, (-1 : ℝ)^n * F n k.val * (-1 : ℝ)^k.val * canonicalLowerInverse F k.val j)
termination_by n

theorem canonicalLowerInverse_diag (F : NatMatrix) (n : ℕ) :
    canonicalLowerInverse F n n = 1 := by rw [canonicalLowerInverse]; simp

theorem canonicalLowerInverse_upper (F : NatMatrix) {n j : ℕ} (hn : n < j) :
    canonicalLowerInverse F n j = 0 := by
  rw [canonicalLowerInverse, ite_eq_right (by omega), ite_eq_left hn]

theorem canonicalLowerInverse_equation (F : NatMatrix)
    (hF : ∀ d, UnitLower d F) (d : ℕ) :
    checker (finiteMatrix d F) * finiteMatrix d (canonicalLowerInverse F) = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [checker_entry, finiteMatrix, Matrix.of_apply, Matrix.one_apply]
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ =>
    (-1 : ℝ)^i.val * F i.val k * (-1 : ℝ)^k * canonicalLowerInverse F k j.val)]
  have hs : (∑ k ∈ range d, (-1 : ℝ)^i.val * F i.val k * (-1 : ℝ)^k *
      canonicalLowerInverse F k j.val) =
    ∑ k ∈ range (i.val+1), (-1 : ℝ)^i.val * F i.val k * (-1 : ℝ)^k *
      canonicalLowerInverse F k j.val := by
    symm
    apply sum_subset (range_mono (by omega))
    intro k hk hki
    rw [(hF d).2 i.val i.isLt k (mem_range.mp hk) (by simpa using hki)]
    ring
  rw [hs, sum_range_succ, (hF d).1 i.val i.isLt, mul_one, sign_square, one_mul]
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl, canonicalLowerInverse_diag]
    have hz : (∑ k ∈ range i.val, (-1 : ℝ)^i.val * F i.val k * (-1 : ℝ)^k *
        canonicalLowerInverse F k i.val) = 0 := by
      apply sum_eq_zero
      intro k hk
      rw [canonicalLowerInverse_upper F (mem_range.mp hk), mul_zero]
    rw [hz, zero_add]
  · rw [ite_eq_right hij]
    by_cases hlt : i.val < j.val
    · rw [canonicalLowerInverse_upper F hlt]
      have hz : (∑ k ∈ range i.val, (-1 : ℝ)^i.val * F i.val k * (-1 : ℝ)^k *
          canonicalLowerInverse F k j.val) = 0 := by
        apply sum_eq_zero
        intro k hk
        rw [canonicalLowerInverse_upper F ((mem_range.mp hk).trans hlt), mul_zero]
      rw [hz, zero_add]
    · rw [canonicalLowerInverse, ite_eq_right (by exact fun h => hij (Fin.ext h)),
        ite_eq_right hlt,
        Fin.sum_univ_eq_sum_range (fun k : ℕ => (-1 : ℝ)^i.val * F i.val k *
          (-1 : ℝ)^k * canonicalLowerInverse F k j.val), add_neg_cancel]

theorem canonicalLowerInverse_signed (F : NatMatrix)
    (hF : ∀ d, UnitLower d F) : SignedInverse F (canonicalLowerInverse F) := by
  intro d
  rw [checker_inverse _ (by rw [unitLower_det (hF d)]; exact isUnit_one)]
  symm
  exact Matrix.inv_eq_right_inv (canonicalLowerInverse_equation F hF d)

#print axioms canonicalLowerInverse_signed
end BTP.SemiInfinite
