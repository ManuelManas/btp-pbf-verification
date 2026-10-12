import OneFactorFormula

/-! # Dependence on arbitrary initial values, before taking any quotients -/
open Matrix Finset Filter
open scoped Topology
noncomputable section
namespace BTP.SemiInfinite
open Extraction InverseBounds

def recurrenceCoefficient (r : ℕ) (F : NatMatrix) (n : ℕ) (i : Fin (r + 1)) : ℝ :=
  (-1 : ℝ)^(r - i.val) * F (n - (r + 1) + i.val) (n - (r + 1)) /
    F n (n - (r + 1))

def fundamental (r : ℕ) (F : NatMatrix) (n : ℕ) (j : Fin (r + 1)) : ℝ :=
  if _hn : n < r + 1 then (if n = j.val then 1 else 0)
  else ∑ i : Fin (r + 1), recurrenceCoefficient r F n i *
    fundamental r F (n - (r + 1) + i.val) j
termination_by n
decreasing_by have := i.isLt; omega

theorem fundamental_initial (r : ℕ) (F : NatMatrix) {n : ℕ} (hn : n < r + 1)
    (j : Fin (r + 1)) : fundamental r F n j = if n = j.val then 1 else 0 := by
  rw [fundamental, dite_eq_left hn]

theorem fundamental_step (r : ℕ) (F : NatMatrix) (n : ℕ) :
    fundamental r F (n + r + 1) =
      ∑ i : Fin (r + 1), recurrenceCoefficient r F (n + r + 1) i • fundamental r F (n + i.val) := by
  funext j
  rw [fundamental, dite_eq_right (show ¬ n + r + 1 < r + 1 by omega)]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    show n + r + 1 - (r + 1) = n by omega]

theorem fundamental_window_nonzero (r : ℕ) (F : NatMatrix)
    (hF : ∀ d, UnitLower d F)
    (hext : ∀ n, r + 1 ≤ n → F n (n - (r + 1)) ≠ 0) (n : ℕ) :
    windowDet (r + 1) (fundamental r F) n ≠ 0 := by
  induction n with
  | zero =>
    have he : (Matrix.of fun i j : Fin (r + 1) => fundamental r F (0 + i.val) j) = 1 := by
      ext i j
      simp only [Matrix.of_apply, Nat.zero_add, fundamental_initial r F i.isLt,
        Matrix.one_apply, Fin.ext_iff]
    unfold windowDet
    rw [he, Matrix.det_one]
    norm_num
  | succ n ih =>
    rw [windowDet_shift (fundamental r F) (recurrenceCoefficient r F (n + r + 1))
      (fundamental_step r F n)]
    apply mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) ?_) ih
    unfold recurrenceCoefficient
    simp only [Fin.val_zero, Nat.sub_zero, Nat.add_zero,
      show n + r + 1 - (r + 1) = n by omega]
    rw [(hF (n + 1)).1 n (by omega), mul_one]
    exact div_ne_zero (pow_ne_zero _ (by norm_num))
      (by simpa only [show n + r + 1 - (r + 1) = n by omega] using hext (n + r + 1) (by omega))

/-- No output value is the zero linear functional of the initial data. -/
theorem fundamental_row_nonzero (r : ℕ) (F : NatMatrix)
    (hF : ∀ d, UnitLower d F)
    (hext : ∀ n, r + 1 ≤ n → F n (n - (r + 1)) ≠ 0) (n : ℕ) :
    ∃ j : Fin (r + 1), fundamental r F n j ≠ 0 := by
  by_cases hn : n < r + 1
  · refine ⟨⟨n, hn⟩, ?_⟩
    rw [fundamental_initial r F hn]
    simp
  · by_contra h
    push Not at h
    have hz : windowDet (r + 1) (fundamental r F) (n - r) = 0 := by
      apply Matrix.det_eq_zero_of_row_eq_zero (Fin.last r)
      intro j
      change fundamental r F (n - r + r) j = 0
      rw [show n - r + r = n by omega]
      exact h j
    exact fundamental_window_nonzero r F hF hext (n - r) hz

theorem canonical_ascending (r : ℕ) (F : NatMatrix) (θ : ℕ → ℝ)
    {n : ℕ} (hn : r + 1 ≤ n) :
    canonicalSequence (r + 1) (by omega) F θ n =
      ∑ i : Fin (r + 1), recurrenceCoefficient r F n i *
        canonicalSequence (r + 1) (by omega) F θ (n - (r + 1) + i.val) := by
  rw [canonicalSequence, dite_eq_right (show ¬ n < r + 1 by omega)]
  rw [← sum_range_reflect (fun j => (-1 : ℝ)^j * F (n - (j + 1)) (n - (r + 1)) *
    canonicalSequence (r + 1) (by omega) F θ (n - (j + 1))) (r + 1)]
  rw [sum_div]
  unfold recurrenceCoefficient
  rw [Fin.sum_univ_eq_sum_range (fun i =>
    ((-1 : ℝ)^(r - i) * F (n - (r + 1) + i) (n - (r + 1)) / F n (n - (r + 1))) *
      canonicalSequence (r + 1) (by omega) F θ (n - (r + 1) + i))]
  apply sum_congr rfl
  intro i hi
  have hi' := mem_range.mp hi
  rw [show r + 1 - 1 - i = r - i by omega,
    show n - (r - i + 1) = n - (r + 1) + i by omega]
  ring

theorem canonical_fundamental (r : ℕ) (F : NatMatrix) (θ : ℕ → ℝ) (n : ℕ) :
    canonicalSequence (r + 1) (by omega) F θ n =
      ∑ j : Fin (r + 1), fundamental r F n j * initialValue (r + 1) θ j.val := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < r + 1
    · rw [canonical_initial (r + 1) (by omega) F θ n hn]
      simp only [fundamental_initial r F hn]
      rw [sum_eq_single (⟨n, hn⟩ : Fin (r + 1))]
      · simp
      · intro j _ hj
        have hne : n ≠ j.val := fun e => hj (Fin.ext e.symm)
        simp [hne]
      · simp
    · rw [canonical_ascending r F θ (by omega)]
      have he : ∀ j, fundamental r F n j = ∑ i : Fin (r + 1),
          recurrenceCoefficient r F n i * fundamental r F (n - (r + 1) + i.val) j := by
        intro j; rw [fundamental, dite_eq_right hn]
      simp only [he, sum_mul]
      rw [sum_comm]
      apply sum_congr rfl
      intro i _
      rw [ih (n - (r + 1) + i.val) (by have := i.isLt; omega), mul_sum]
      apply sum_congr rfl
      intro j _
      ring

#print axioms fundamental_row_nonzero
#print axioms canonical_fundamental
end BTP.SemiInfinite
