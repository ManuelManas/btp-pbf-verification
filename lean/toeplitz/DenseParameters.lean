import RecurrenceParameters

/-! # Nonvanishing initial data form a dense set -/
open Matrix Finset Filter
open scoped Topology
noncomputable section
namespace BTP.SemiInfinite
open Extraction

def affineValue {r : ℕ} (u : Fin (r + 1) → ℝ) (x : Fin r → ℝ) : ℝ :=
  (∑ i : Fin r, u i.castSucc * x i) + u (Fin.last r)

theorem affineValue_continuous {r : ℕ} (u : Fin (r + 1) → ℝ) :
    Continuous (affineValue u) := by
  unfold affineValue
  fun_prop

theorem affineValue_nonzero_dense {r : ℕ} (u : Fin (r + 1) → ℝ)
    (hu : ∃ j, u j ≠ 0) : Dense {x : Fin r → ℝ | affineValue u x ≠ 0} := by
  by_cases hfree : ∃ i : Fin r, u i.castSucc ≠ 0
  · obtain ⟨i, hi⟩ := hfree
    intro x
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    by_cases hx : affineValue u x = 0
    · let z : Fin r → ℝ := fun j => if j = i then ε / 2 else 0
      let y := x + z
      have hy : affineValue u y = u i.castSucc * (ε / 2) := by
        have he : affineValue u y = affineValue u x + ∑ j : Fin r, u j.castSucc * z j := by
          simp only [affineValue, y, Pi.add_apply, mul_add, sum_add_distrib]
          ring
        rw [he, hx, zero_add, sum_eq_single i]
        · simp [z]
        · intro j _ hj; simp [z, hj]
        · simp
      have hnorm : ‖x - y‖ ≤ ε / 2 := by
        apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
        intro j
        by_cases hj : j = i
        · subst j
          simp only [y, z, Pi.sub_apply, Pi.add_apply, ite_true, sub_add_cancel_left,
            norm_neg, Real.norm_eq_abs, abs_of_pos (show 0 < ε / 2 by positivity)]
          exact le_rfl
        · simp only [y, z, Pi.sub_apply, Pi.add_apply, ite_eq_right hj, add_zero,
            sub_self, norm_zero]
          positivity
      refine ⟨y, ?_, ?_⟩
      · change affineValue u y ≠ 0
        rw [hy]
        exact mul_ne_zero hi (by positivity)
      · rw [dist_eq_norm]
        exact lt_of_le_of_lt hnorm (by linarith)
    · exact ⟨x, hx, by simpa using hε⟩
  · have hz : ∀ i : Fin r, u i.castSucc = 0 := by simpa only [not_exists, not_not] using hfree
    have hlast : u (Fin.last r) ≠ 0 := by
      obtain ⟨j, hj⟩ := hu
      induction j using Fin.lastCases with
      | last => exact hj
      | cast i => exact (hj (hz i)).elim
    have hall : ∀ x : Fin r → ℝ, affineValue u x ≠ 0 := by
      intro x; simpa [affineValue, hz] using hlast
    have he : {x : Fin r → ℝ | affineValue u x ≠ 0} = Set.univ := by ext x; simp [hall x]
    rw [he]
    exact dense_univ

def GoodInitialData (r : ℕ) (F : NatMatrix) : Set (Fin r → ℝ) :=
  {x | ∀ n, affineValue (fundamental r F n) x ≠ 0}

/-- All recurrence values are simultaneously nonzero on a dense set of data.
This uses Baire's theorem for the finite-dimensional real parameter space. -/
theorem goodInitialData_dense (r : ℕ) (F : NatMatrix)
    (hF : ∀ d, UnitLower d F)
    (hext : ∀ n, r + 1 ≤ n → F n (n - (r + 1)) ≠ 0) :
    Dense (GoodInitialData r F) := by
  have hopen : ∀ n, IsOpen {x : Fin r → ℝ | affineValue (fundamental r F n) x ≠ 0} := by
    intro n
    exact isOpen_ne.preimage (affineValue_continuous _)
  have hdense : ∀ n, Dense {x : Fin r → ℝ | affineValue (fundamental r F n) x ≠ 0} :=
    fun n => affineValue_nonzero_dense _ (fundamental_row_nonzero r F hF hext n)
  have h := dense_iInter_of_isOpen_nat hopen hdense
  simpa only [GoodInitialData, Set.iInter_ofPred] using h

#print axioms goodInitialData_dense
end BTP.SemiInfinite
