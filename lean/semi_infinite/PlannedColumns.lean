import UniformPerturbation

/-! # Choosing all initial entries in a single neighborhood

Stage l removes l factors from the left, leaving bandwidth p-l.
The first p-l inverse columns can be computed from the initial entries alone.
No factorization is assumed in the definition of these columns.
-/
open Matrix Finset Filter
open scoped Topology
noncomputable section
namespace BTP.SemiInfinite
open Extraction

def columnCoefficients (p : ℕ) (u : Parameters p) : ℕ → Fin p → ℕ → ℝ
  | 0, h, j => if h.val = j then 1 else 0
  | l + 1, h, j => columnCoefficients p u l h j -
      freeValue p u (p - (l + 1)) (j + 1) * columnCoefficients p u l h (j + 1)

def plannedInverse (Q : NatMatrix) (p : ℕ) (u : Parameters p)
    (l n j : ℕ) : ℝ :=
  ∑ h : Fin p, Q n h.val * columnCoefficients p u l h j

theorem columnCoefficients_zero (p l : ℕ) (h : Fin p) (j : ℕ) :
    columnCoefficients p 0 l h j = if h.val = j then 1 else 0 := by
  induction l with
  | zero => rfl
  | succ l ih => simp only [columnCoefficients, freeValue_zero, zero_mul, sub_zero, ih]

theorem columnCoefficients_continuous (p l : ℕ) (h : Fin p) (j : ℕ) :
    ContinuousAt (fun u => columnCoefficients p u l h j) 0 := by
  induction l generalizing j with
  | zero => exact continuousAt_const
  | succ l ih =>
    exact (ih j).sub ((freeValue_analytic p (p - (l + 1)) (j + 1)).continuousAt.mul
      (ih (j + 1)))

theorem plannedInverse_zero (Q : NatMatrix) (p l n j : ℕ) (hj : j < p) :
    plannedInverse Q p 0 l n j = Q n j := by
  unfold plannedInverse
  simp only [columnCoefficients_zero]
  rw [sum_eq_single (⟨j, hj⟩ : Fin p)]
  · simp
  · intro h _ hh
    have hv : h.val ≠ j := by intro e; apply hh; exact Fin.ext e
    simp [hv]
  · simp

theorem plannedInverse_initial (Q : NatMatrix) (p : ℕ) (u : Parameters p)
    (n j : ℕ) (hj : j < p) : plannedInverse Q p u 0 n j = Q n j := by
  have he : plannedInverse Q p u 0 n j = plannedInverse Q p 0 0 n j := rfl
  rw [he, plannedInverse_zero Q p 0 n j hj]

theorem plannedInverse_succ (Q : NatMatrix) (p : ℕ) (u : Parameters p)
    (l n j : ℕ) :
    plannedInverse Q p u (l + 1) n j = plannedInverse Q p u l n j -
      freeValue p u (p - (l + 1)) (j + 1) * plannedInverse Q p u l n (j + 1) := by
  simp only [plannedInverse, columnCoefficients, mul_sub, sum_sub_distrib, mul_sum]
  congr 1
  apply sum_congr rfl
  intro h _
  ring

def plannedWindow (Q : NatMatrix) (p : ℕ) (u : Parameters p) (l n : ℕ) : ℝ :=
  windowDet (p - l) (fun t j => plannedInverse Q p u l t j.val) n

theorem plannedWindow_mul (Q : NatMatrix) (p : ℕ) (u : Parameters p) (l n : ℕ) :
    plannedWindow Q p u l n =
      ((Matrix.of fun (i : Fin (p - l)) (h : Fin p) => Q (n + i.val) h.val) *
        (Matrix.of fun (h : Fin p) (j : Fin (p - l)) => columnCoefficients p u l h j.val)).det := by
  rfl

theorem planned_windows_positive {p : ℕ} {a : Entries} (ha : Metelmann p a)
    (hs : ∀ k, 0 < k → k < p → Summable (adjacentTerm a k)) :
    ∀ᶠ u in 𝓝 (0 : Parameters p), ∀ l ≤ p, ∀ n,
      0 < plannedWindow (inverseEntries a p) p u l n := by
  obtain ⟨B, hB, hbound⟩ := uniform_inverse_minors ha hs
  have he : ∀ l : Fin (p + 1), ∀ᶠ u in 𝓝 (0 : Parameters p), ∀ n,
      0 < plannedWindow (inverseEntries a p) p u l.val n := by
    intro l
    let A := fun n => Matrix.of fun (i : Fin (p - l.val)) (h : Fin p) =>
      inverseEntries a p (n + i.val) h.val
    let C := fun u : Parameters p => Matrix.of fun (h : Fin p) (j : Fin (p - l.val)) =>
      columnCoefficients p u l.val h j.val
    let δ := fun n => consecutiveMinor a p (p - l.val) n (fun j => j.val)
    have hz : ∀ n, (A n * C 0).det = δ n := by
      intro n
      rw [← plannedWindow_mul]
      unfold plannedWindow windowDet δ consecutiveMinor
      congr 1
      ext i j
      exact plannedInverse_zero _ _ _ _ _ (by omega)
    have hpos := uniform_determinant_positivity A δ C
      (fun n => leading_minor_pos ha (Nat.sub_le _ _) n) hz
      (fun h j => columnCoefficients_continuous p l.val h j.val)
      (fun n c => hbound (p - l.val) (Nat.sub_le _ _) n (fun j => (c j).val)
        (fun j => (c j).isLt))
    simpa only [plannedWindow_mul] using hpos
  filter_upwards [eventually_all.mpr he] with u hu
  intro l hl n
  exact hu ⟨l, by omega⟩ n

#print axioms planned_windows_positive
end BTP.SemiInfinite
