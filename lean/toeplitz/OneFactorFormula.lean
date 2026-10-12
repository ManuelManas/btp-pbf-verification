import GlobalConstruction

/-! # The extraction matrix and its determinant formula

The algebraic formula below is proved when the recurrence values are nonzero.
The positivity implication was proved separately in ExtractionPositive without
assuming nonvanishing. It therefore supplies this hypothesis in the application
to global positive factorization, without circular reasoning.
-/
open Matrix Finset
noncomputable section
namespace BTP.SemiInfinite
open Extraction InverseBounds

def extractionMatrix (m : ℕ) (θ : ℕ → ℝ) : Matrix (Fin m) (Fin (m - 1)) ℝ :=
  fun i j => (if i.val = j.val then 1 else 0) -
    (if i.val = j.val + 1 then θ (j.val + 1) else 0)

theorem extractionColumns_matrix {m : ℕ} (hm : 0 < m) (R : NatMatrix) (θ : ℕ → ℝ)
    (n : ℕ) :
    (Matrix.of fun i j : Fin (m - 1) => extractionColumns R θ m (n + i.val) j) =
      (Matrix.of fun (i : Fin (m - 1)) (h : Fin m) => R (n + i.val) h.val) *
        extractionMatrix m θ := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.of_apply, extractionMatrix, mul_sub, sum_sub_distrib]
  have h0 : (∑ h : Fin m, R (n + i.val) h.val * (if h.val = j.val then 1 else 0)) =
      R (n + i.val) j.val := by
    rw [sum_eq_single (⟨j.val, by omega⟩ : Fin m)]
    · simp
    · intro h _ hh
      have hv : h.val ≠ j.val := fun e => hh (Fin.ext e)
      simp [hv]
    · simp
  have h1 : (∑ h : Fin m, R (n + i.val) h.val *
      (if h.val = j.val + 1 then θ (j.val + 1) else 0)) =
      R (n + i.val) (j.val + 1) * θ (j.val + 1) := by
    rw [sum_eq_single (⟨j.val + 1, by omega⟩ : Fin m)]
    · simp
    · intro h _ hh
      have hv : h.val ≠ j.val + 1 := fun e => hh (Fin.ext e)
      simp [hv]
    · simp
  rw [h0, h1]
  unfold extractionColumns
  ring

theorem signedInverse_diagonal {F R : NatMatrix} (hF : ∀ d, UnitLower d F)
    (hR : SignedInverse F R) (n : ℕ) : R n n = 1 := by
  have he := congrArg (fun M : Square (n + 1) => M ⟨n, by omega⟩ ⟨n, by omega⟩)
    (signedInverse_equation hF hR (n + 1))
  rw [Matrix.mul_apply] at he
  simp only [checker_entry, finiteMatrix, Matrix.of_apply, Matrix.one_apply, ite_true] at he
  rw [sum_eq_single (⟨n, by omega⟩ : Fin (n + 1))] at he
  · rw [(hF (n + 1)).1 n (by omega), mul_one, sign_square, one_mul] at he
    exact he
  · intro k _ hk
    have hv : k.val < n := by
      have hne : k.val ≠ n := fun e => hk (Fin.ext e)
      omega
    rw [signedInverse_upper hF hR hv, mul_zero]
  · simp

theorem extraction_initial_determinant {m : ℕ} {F R : NatMatrix}
    (hF : ∀ d, UnitLower d F) (hR : SignedInverse F R) (θ : ℕ → ℝ) :
    windowDet (m - 1) (extractionColumns R θ m) 0 = 1 := by
  let M := Matrix.of fun i j : Fin (m - 1) => extractionColumns R θ m i.val j
  simp only [windowDet, Nat.zero_add]
  change M.det = 1
  have ht : M.IsLowerTriangular := by
    intro i j hij
    change i.val < j.val at hij
    change R i.val j.val - θ (j.val + 1) * R i.val (j.val + 1) = 0
    rw [signedInverse_upper hF hR hij, signedInverse_upper hF hR (by omega)]
    ring
  rw [Matrix.det_of_isLowerTriangular M ht]
  apply prod_eq_one
  intro i _
  change R i.val i.val - θ (i.val + 1) * R i.val (i.val + 1) = 1
  rw [signedInverse_diagonal hF hR, signedInverse_upper hF hR (by omega)]
  ring

/-- The exact formula on the nonvanishing domain of the extraction recurrence. -/
theorem extraction_determinant_formula {m : ℕ} (hm : 2 ≤ m) (F R : NatMatrix)
    (θ : ℕ → ℝ) (hF : ∀ d, UnitLower d F) (hb : ∀ d, Bandwidth d m F)
    (hext : ∀ n, m ≤ n → F n (n - m) ≠ 0) (hR : SignedInverse F R)
    (hθ : ∀ n, 0 < n → n < m → θ n ≠ 0)
    (hφ : ∀ n, canonicalSequence m (by omega) F θ n ≠ 0) (n : ℕ) :
    windowDet (m - 1) (extractionColumns R θ m) n =
      (∏ t ∈ Ico m (n + m), F t (t - m)) * canonicalSequence m (by omega) F θ (n + m - 1) := by
  let φ := canonicalSequence m (by omega) F θ
  let a := fun t => φ (t - 1) / φ t
  let H := remainder a F
  let S := removedInverse R a
  have ha : ∀ t, 0 < t → t < m → a t = θ t :=
    initial_ratios m (by omega) θ φ hθ (canonical_initial m (by omega) F θ)
  have hH : ∀ d, UnitLower d H := fun d => remainder_unit d a F (hF d)
  have hS : SignedInverse H S := signedInverse_remainder hF hR a
  have hbH : ∀ d, Bandwidth d (m - 1) H := by
    intro d
    apply remainder_bandwidth d m (by omega) a φ F (hb d)
      (quotient_relation d φ (fun t _ => hφ t)) (fun t _ => hφ t)
    exact canonical_recurrence d m (by omega) F θ (fun t ht _ => hext t ht)
  have heW : ∀ t, windowDet (m - 1) (fun v j => S v j.val) t =
      windowDet (m - 1) (extractionColumns R θ m) t := by
    intro t
    unfold windowDet
    congr 1
    ext i j
    dsimp [S, removedInverse, extractionColumns]
    rw [ha (j.val + 1) (by omega) (by omega)]
    ring
  have hstep : ∀ t, φ (t + m - 1) * H (t + m - 1) t = F (t + m) t * φ (t + m) := by
    intro t
    have he := weighted_remainder (t + m) a φ F
      (quotient_relation (t + m) φ (fun v _ => hφ v)) t (m - 1) (by omega)
    have hx : t + (m - 1) = t + m - 1 := by omega
    rw [hx] at he
    have hr := canonical_recurrence (t + m + 1) m (by omega) F θ
      (fun v hv _ => hext v hv) (t + m) (by omega) (by omega)
    change F (t + m) (t + m - m) * φ (t + m) = rhs m F φ (t + m) at hr
    rw [Nat.add_sub_cancel] at hr
    rw [hr]
    unfold H remainder
    rw [ite_eq_left (show t ≤ t + m - 1 by omega),
      show t + m - 1 - t = m - 1 by omega, he]
    simp only [rhs, show m - 1 + 1 = m by omega]
    apply sum_congr rfl
    intro j _
    rw [show t + m - 1 - j = t + m - (j + 1) by omega]
    simp only [Nat.add_sub_cancel]
  induction n with
  | zero =>
    rw [extraction_initial_determinant hF hR]
    simp only [Nat.zero_add, Ico_self, prod_empty, one_mul]
    rw [canonical_initial m (by omega) F θ (m - 1) (by omega)]
    simp [initialValue]
  | succ n ih =>
    have he := inverse_window_det hH hS (m - 2) n
      (by simpa only [show m - 2 + 1 = m - 1 by omega] using hbH (n + (m - 2) + 2))
    rw [show m - 2 + 1 = m - 1 by omega,
      show n + (m - 2) + 1 = n + m - 1 by omega, heW, heW] at he
    rw [he, ih]
    rw [show n + 1 + m = (n + m) + 1 by omega,
      prod_Ico_succ_top (show m ≤ n + m by omega)]
    simp only [Nat.add_sub_cancel]
    change H (n + m - 1) n * ((∏ t ∈ Ico m (n + m), F t (t - m)) * φ (n + m - 1)) = _
    calc
      _ = (∏ t ∈ Ico m (n + m), F t (t - m)) *
          (φ (n + m - 1) * H (n + m - 1) n) := by ring
      _ = _ := by rw [hstep]; ring

#print axioms extractionColumns_matrix
#print axioms extraction_determinant_formula
end BTP.SemiInfinite
