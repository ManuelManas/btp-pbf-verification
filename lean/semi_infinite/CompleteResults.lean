import TwoSidedCriterion
import UnrestrictedDeterminant

/-! # Complete statements added in version 02 (2026-10-08)

1. A PBF exists if and only if all p+q-2 actual inverse-minor limits are positive.
2. The extraction determinant identity holds for ALL initial parameters,
   including zeros of the initial entries and of the recurrence solution.
-/
open Matrix Finset
noncomputable section
namespace BTP.SemiInfinite
open Extraction

theorem global_two_sided_criterion_complete {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {a c : Entries} {D : ℕ → ℝ}
    (ha : Metelmann p a) (hc : Metelmann q c) (hD : ∀ n, 0 < D n) :
    (HasTwoSidedPBF p q a c D ↔ ∀ i : ObstructionIndex p q, 0 < twoSidedLimit p q a c i) ∧
      Fintype.card (ObstructionIndex p q) = p + q - 2 :=
  ⟨two_sided_PBF_iff_positive_limits hp hq ha hc hD, number_of_limits hp hq⟩

/-- Literal rectangular-matrix version of the determinant identity in the paper. -/
theorem one_factor_determinant_formula_complete {m : ℕ} (hm : 2 ≤ m)
    (F R : NatMatrix) (θ : ℕ → ℝ)
    (hF : ∀ d, UnitLower d F) (hb : ∀ d, Bandwidth d m F)
    (hext : ∀ n, m ≤ n → F n (n - m) ≠ 0) (hR : SignedInverse F R) (n : ℕ) :
    ((Matrix.of fun (i : Fin (m - 1)) (j : Fin m) => R (n + i.val) j.val) *
        extractionMatrix m θ).det =
      (∏ t ∈ Ico m (n + m), F t (t - m)) *
        canonicalSequence m (by omega) F θ (n + m - 1) := by
  rw [← extractionColumns_matrix (by omega) R θ n]
  exact extraction_determinant_formula_unrestricted hm F R θ hF hb hext hR n

/- A concrete boundary case: F=(I+Λᵀ)^2 and θ₁=2 gives φ₂=0.
The unrestricted theorem applies, whereas the old nonvanishing theorem cannot. -/
theorem example_recurrence_zero :
    canonicalSequence 2 (by omega) (productEntries (fun _ _ => 1) 2) (fun _ => 2) 2 = 0 := by
  have h0 : canonicalSequence 2 (by omega) (productEntries (fun _ _ => 1) 2) (fun _ => 2) 0 = 2 := by
    rw [canonical_initial 2 (by omega) _ _ 0 (by omega)]
    norm_num [initialValue]
  have h1 : canonicalSequence 2 (by omega) (productEntries (fun _ _ => 1) 2) (fun _ => 2) 1 = 1 := by
    rw [canonical_initial 2 (by omega) _ _ 1 (by omega)]
    norm_num [initialValue]
  have hc := canonical_recurrence 3 2 (by omega) (productEntries (fun _ _ => 1) 2) (fun _ => 2)
    (fun n hn hnd => (product_outer_positive 3 2 (fun _ _ => 1)
      (by intro j hj t ht htd; norm_num) n hn hnd).ne') 2 (by omega) (by omega)
  norm_num [rhs, sum_range_succ, productEntries, entry, h0, h1] at hc
  exact hc

theorem example_extraction_at_zero :
    windowDet 1 (extractionColumns (inverseEntries (fun _ _ => 1) 2) (fun _ => 2) 2) 1 = 0 := by
  have h := extraction_determinant_formula_unrestricted (m := 2) (by omega)
    (productEntries (fun _ _ => 1) 2) (inverseEntries (fun _ _ => 1) 2) (fun _ => 2)
    (fun d => product_unit d _ 2) (fun d => product_band d _ 2)
    (fun n hn => (product_outer_positive (n + 1) 2 (fun _ _ => 1)
      (by intro j hj t ht htd; norm_num) n hn (by omega)).ne')
    (metelmann_signedInverse 2 (fun _ _ => 1)) 1
  simpa only [show 1 + 2 - 1 = 2 by omega, example_recurrence_zero, mul_zero] using h

#print axioms global_two_sided_criterion_complete
#print axioms one_factor_determinant_formula_complete
#print axioms PBF_gives_positive_limits
#print axioms normalized_products_unique
#print axioms goodInitialData_dense
#print axioms example_extraction_at_zero
end BTP.SemiInfinite
