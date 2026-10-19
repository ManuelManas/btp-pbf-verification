import DenseParameters

/-! # Recovering the initial ratios and taking limits without dividing by zeros -/
open Matrix Finset Filter
open scoped Topology
noncomputable section
namespace BTP.SemiInfinite
open Extraction

def dataValue {r : ℕ} (x : Fin r → ℝ) (n : ℕ) : ℝ :=
  if hn : n < r then x ⟨n, hn⟩ else 1

def chartTheta {r : ℕ} (x : Fin r → ℝ) (n : ℕ) : ℝ := dataValue x (n - 1) / dataValue x n

theorem dataValue_nonzero {r : ℕ} (x : Fin r → ℝ) (hx : ∀ i, x i ≠ 0) (n : ℕ) :
    dataValue x n ≠ 0 := by
  unfold dataValue
  split_ifs with h
  · exact hx _
  · norm_num

theorem chartTheta_initial {r : ℕ} (x : Fin r → ℝ) (hx : ∀ i, x i ≠ 0)
    {n : ℕ} (hn : n ≤ r) : initialValue (r + 1) (chartTheta x) n = dataValue x n := by
  have hp : ∀ N, n ≤ N →
      (∏ t ∈ Ico n N, chartTheta x (t + 1)) = dataValue x n / dataValue x N := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base => simp [dataValue_nonzero x hx]
    | succ N hN ih =>
      rw [prod_Ico_succ_top hN, ih]
      unfold chartTheta
      simp only [Nat.add_sub_cancel]
      field_simp [dataValue_nonzero x hx N]
  unfold initialValue
  simp only [Nat.add_sub_cancel]
  rw [hp r hn]
  simp [dataValue]

theorem affine_fundamental_initial (r : ℕ) (F : NatMatrix) (x : Fin r → ℝ)
    (j : Fin (r + 1)) : affineValue (fundamental r F j.val) x = dataValue x j.val := by
  unfold affineValue
  simp only [fundamental_initial r F j.isLt, Fin.val_castSucc, Fin.val_last]
  induction j using Fin.lastCases with
  | last =>
    simp only [Fin.val_last, ite_true, dataValue, lt_self_iff_false, dite_false]
    have hz : (∑ i : Fin r, (if r = i.val then (1 : ℝ) else 0) * x i) = 0 := by
      apply sum_eq_zero
      intro i _
      simp [show r ≠ i.val by omega]
    rw [hz, zero_add]
  | cast j =>
    simp only [Fin.val_castSucc, ite_eq_right (show j.val ≠ r by omega), add_zero,
      dataValue, dite_eq_left j.isLt]
    rw [sum_eq_single j]
    · simp
    · intro i _ hi
      have hne : j.val ≠ i.val := fun e => hi (Fin.ext e.symm)
      simp [hne]
    · simp

theorem goodInitialData_coordinates {r : ℕ} {F : NatMatrix} {x : Fin r → ℝ}
    (hx : x ∈ GoodInitialData r F) : ∀ i, x i ≠ 0 := by
  intro i
  have h := hx i.val
  change affineValue (fundamental r F i.castSucc.val) x ≠ 0 at h
  rw [affine_fundamental_initial r F x i.castSucc] at h
  simpa only [Fin.val_castSucc, dataValue, dite_eq_left i.isLt] using h

theorem canonical_chart (r : ℕ) (F : NatMatrix) (x : Fin r → ℝ)
    (hx : ∀ i, x i ≠ 0) (n : ℕ) :
    canonicalSequence (r + 1) (by omega) F (chartTheta x) n =
      affineValue (fundamental r F n) x := by
  rw [canonical_fundamental]
  have he : ∀ j : Fin (r + 1), initialValue (r + 1) (chartTheta x) j.val = dataValue x j.val :=
    fun j => chartTheta_initial x hx (by omega)
  simp only [he]
  rw [Fin.sum_univ_castSucc]
  simp [affineValue, dataValue]

theorem chartTheta_continuousAt {r : ℕ} (x : Fin r → ℝ) (hx : ∀ i, x i ≠ 0) (n : ℕ) :
    ContinuousAt (fun y : Fin r → ℝ => chartTheta y n) x := by
  have hv : ∀ t, Continuous (fun y : Fin r → ℝ => dataValue y t) := by
    intro t
    unfold dataValue
    split_ifs
    · fun_prop
    · exact continuous_const
  exact (hv (n - 1)).continuousAt.div (hv n).continuousAt (dataValue_nonzero x hx n)

theorem canonical_continuousAt {E : Type*} [TopologicalSpace E]
    (r : ℕ) (F : NatMatrix) (Θ : E → ℕ → ℝ) (x : E)
    (hΘ : ∀ n, ContinuousAt (fun y => Θ y n) x) (n : ℕ) :
    ContinuousAt (fun y => canonicalSequence (r + 1) (by omega) F (Θ y) n) x := by
  have he : (fun y => canonicalSequence (r + 1) (by omega) F (Θ y) n) =
      (fun y => ∑ j : Fin (r + 1), fundamental r F n j * initialValue (r + 1) (Θ y) j.val) := by
    funext y; exact canonical_fundamental r F (Θ y) n
  rw [he]
  unfold initialValue
  fun_prop

theorem extractionWindow_continuousAt {E : Type*} [TopologicalSpace E]
    (r : ℕ) (R : NatMatrix) (Θ : E → ℕ → ℝ) (x : E)
    (hΘ : ∀ n, ContinuousAt (fun y => Θ y n) x) (n : ℕ) :
    ContinuousAt (fun y => windowDet r (extractionColumns R (Θ y) (r + 1)) n) x := by
  unfold windowDet
  simp only [Matrix.det_apply, Matrix.of_apply, extractionColumns]
  fun_prop

/-- Equality on a dense set passes to a point where both expressions are continuous. -/
theorem dense_equality_at {E : Type*} [PseudoMetricSpace E] {s : Set E} (hs : Dense s)
    {f g : E → ℝ} (he : Set.EqOn f g s) (x : E)
    (hf : ContinuousAt f x) (hg : ContinuousAt g x) : f x = g x := by
  by_contra h
  have hn := (hf.sub hg).eventually_ne (sub_ne_zero.mpr h)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hn
  obtain ⟨y, hy, hdist⟩ := hs.exists_dist_lt x hε
  have hneq := hball (by simpa only [dist_comm] using hdist)
  exact hneq (by change f y - g y = 0; rw [he hy, sub_self])

#print axioms canonical_chart
end BTP.SemiInfinite
