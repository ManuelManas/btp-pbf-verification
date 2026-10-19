import ParameterChart

/-! # The determinant identity holds even when recurrence values vanish

First pass to arbitrary recurrence values with nonzero initial entries.
Then use continuity once more to allow zero initial entries too. No quotient
of a vanishing recurrence value is taken at the point being proved.
-/
open Matrix Finset Filter
open scoped Topology
noncomputable section
namespace BTP.SemiInfinite
open Extraction

theorem initialValue_nonzero (r : ℕ) (θ : ℕ → ℝ)
    (hθ : ∀ n, 0 < n → n < r + 1 → θ n ≠ 0) (n : ℕ) :
    initialValue (r + 1) θ n ≠ 0 := by
  apply prod_ne_zero_iff.mpr
  intro t ht
  have ht' := mem_Ico.mp ht
  exact hθ (t + 1) (by omega) (by omega)

theorem extraction_formula_nonzero_initial (r : ℕ) (hr : 1 ≤ r) (F R : NatMatrix)
    (θ : ℕ → ℝ) (hF : ∀ d, UnitLower d F) (hb : ∀ d, Bandwidth d (r + 1) F)
    (hext : ∀ n, r + 1 ≤ n → F n (n - (r + 1)) ≠ 0) (hR : SignedInverse F R)
    (hθ : ∀ n, 0 < n → n < r + 1 → θ n ≠ 0) (n : ℕ) :
    windowDet r (extractionColumns R θ (r + 1)) n =
      (∏ t ∈ Ico (r + 1) (n + (r + 1)), F t (t - (r + 1))) *
        canonicalSequence (r + 1) (by omega) F θ (n + r) := by
  let x : Fin r → ℝ := fun i => initialValue (r + 1) θ i.val
  have hx : ∀ i, x i ≠ 0 := fun i => initialValue_nonzero r θ hθ i.val
  have hd : ∀ t, t ≤ r → dataValue x t = initialValue (r + 1) θ t := by
    intro t ht
    by_cases hlt : t < r
    · simp only [dataValue, dite_eq_left hlt, x]
    · have he : t = r := by omega
      subst t
      simp [dataValue, initialValue]
  have hparam : ∀ t, 0 < t → t < r + 1 → chartTheta x t = θ t := by
    intro t ht htr
    unfold chartTheta
    rw [hd (t - 1) (by omega), hd t (by omega)]
    exact initial_ratios (r + 1) (by omega) θ (initialValue (r + 1) θ) hθ
      (fun _ _ => rfl) t ht htr
  let f := fun y : Fin r → ℝ => windowDet r (extractionColumns R (chartTheta y) (r + 1)) n
  let g := fun y : Fin r → ℝ =>
    (∏ t ∈ Ico (r + 1) (n + (r + 1)), F t (t - (r + 1))) *
      canonicalSequence (r + 1) (by omega) F (chartTheta y) (n + r)
  have heq : Set.EqOn f g (GoodInitialData r F) := by
    intro y hy
    have hyc := goodInitialData_coordinates hy
    have hyθ : ∀ t, 0 < t → t < r + 1 → chartTheta y t ≠ 0 := by
      intro t _ _
      exact div_ne_zero (dataValue_nonzero y hyc _) (dataValue_nonzero y hyc _)
    have hyφ : ∀ t, canonicalSequence (r + 1) (by omega) F (chartTheta y) t ≠ 0 := by
      intro t
      rw [canonical_chart r F y hyc t]
      exact hy t
    have h := extraction_determinant_formula (m := r + 1) (by omega) F R
      (chartTheta y) hF hb hext hR hyθ hyφ n
    exact h
  have he := dense_equality_at (goodInitialData_dense r F hF hext) heq x
    (extractionWindow_continuousAt r R chartTheta x (chartTheta_continuousAt x hx) n)
    (continuousAt_const.mul (canonical_continuousAt r F chartTheta x
      (chartTheta_continuousAt x hx) (n + r)))
  have hc : extractionColumns R (chartTheta x) (r + 1) = extractionColumns R θ (r + 1) := by
    funext t j
    unfold extractionColumns
    rw [hparam (j.val + 1) (by omega) (by omega)]
  have hφ : canonicalSequence (r + 1) (by omega) F (chartTheta x) (n + r) =
      canonicalSequence (r + 1) (by omega) F θ (n + r) := by
    exact canonical_parameters_ext (n + r + 2) (r + 1) (by omega) F (chartTheta x) θ
      (fun t ht _ => hext t ht) hparam _ (by omega)
  dsimp [f, g] at he
  rw [hc, hφ] at he
  exact he

def liftTheta {r : ℕ} (x : Fin r → ℝ) (n : ℕ) : ℝ :=
  if h : 0 < n ∧ n < r + 1 then x ⟨n - 1, by omega⟩ else 0

theorem liftTheta_continuous {r : ℕ} (n : ℕ) :
    Continuous (fun x : Fin r → ℝ => liftTheta x n) := by
  unfold liftTheta
  split_ifs
  · fun_prop
  · exact continuous_const

theorem nonzero_coordinates_dense (r : ℕ) : Dense {x : Fin r → ℝ | ∀ i, x i ≠ 0} := by
  have hd : ∀ i : Fin r, Dense {x : Fin r → ℝ | x i ≠ 0} := by
    intro i
    let u : Fin (r + 1) → ℝ := fun j => if j = i.castSucc then 1 else 0
    have he : affineValue u = (fun x : Fin r → ℝ => x i) := by
      funext x
      have hlast : Fin.last r ≠ i.castSucc := by intro h; have := congrArg Fin.val h; dsimp at this; omega
      simp [affineValue, u, hlast]
    have h := affineValue_nonzero_dense u ⟨i.castSucc, by simp [u]⟩
    simpa only [he] using h
  have ho : ∀ i : Fin r, IsOpen {x : Fin r → ℝ | x i ≠ 0} :=
    fun i => isOpen_ne.preimage (continuous_apply i)
  simpa only [Set.iInter_ofPred] using dense_iInter_of_isOpen ho hd

/-- The manuscript's algebraic determinant identity, with NO nonvanishing
assumption on the initial parameters or on any recurrence value. -/
theorem extraction_determinant_formula_unrestricted {m : ℕ} (hm : 2 ≤ m)
    (F R : NatMatrix) (θ : ℕ → ℝ)
    (hF : ∀ d, UnitLower d F) (hb : ∀ d, Bandwidth d m F)
    (hext : ∀ n, m ≤ n → F n (n - m) ≠ 0) (hR : SignedInverse F R) (n : ℕ) :
    windowDet (m - 1) (extractionColumns R θ m) n =
      (∏ t ∈ Ico m (n + m), F t (t - m)) *
        canonicalSequence m (by omega) F θ (n + m - 1) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show m ≠ 0 by omega)
  simp only [Nat.succ_eq_add_one] at hm hb hext ⊢
  let x : Fin r → ℝ := fun i => θ (i.val + 1)
  let f := fun y : Fin r → ℝ => windowDet r (extractionColumns R (liftTheta y) (r + 1)) n
  let g := fun y : Fin r → ℝ =>
    (∏ t ∈ Ico (r + 1) (n + (r + 1)), F t (t - (r + 1))) *
      canonicalSequence (r + 1) (by omega) F (liftTheta y) (n + r)
  have heq : Set.EqOn f g {y : Fin r → ℝ | ∀ i, y i ≠ 0} := by
    intro y hy
    apply extraction_formula_nonzero_initial r (by omega) F R (liftTheta y) hF hb hext hR
    intro t ht htr
    simp only [liftTheta, dite_eq_left (show 0 < t ∧ t < r + 1 from ⟨ht, htr⟩)]
    exact hy _
  have he := dense_equality_at (nonzero_coordinates_dense r) heq x
    (extractionWindow_continuousAt r R liftTheta x (fun t => (liftTheta_continuous t).continuousAt) n)
    (continuousAt_const.mul (canonical_continuousAt r F liftTheta x
      (fun t => (liftTheta_continuous t).continuousAt) (n + r)))
  have hparam : ∀ t, 0 < t → t < r + 1 → liftTheta x t = θ t := by
    intro t ht htr
    simp only [liftTheta, dite_eq_left (show 0 < t ∧ t < r + 1 from ⟨ht, htr⟩), x, show t - 1 + 1 = t by omega]
  have hc : extractionColumns R (liftTheta x) (r + 1) = extractionColumns R θ (r + 1) := by
    funext t j
    unfold extractionColumns
    rw [hparam (j.val + 1) (by omega) (by omega)]
  have hφ := canonical_parameters_ext (n + r + 2) (r + 1) (by omega) F (liftTheta x) θ
    (fun t ht _ => hext t ht) hparam (n + r) (by omega)
  dsimp [f, g] at he
  rw [hc, hφ] at he
  exact he

#print axioms extraction_formula_nonzero_initial
#print axioms extraction_determinant_formula_unrestricted
end BTP.SemiInfinite
