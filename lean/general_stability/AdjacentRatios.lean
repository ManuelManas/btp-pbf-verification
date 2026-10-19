import InverseMinors

/-! # Every inverse-minor ratio is the reciprocal of an adjacent partial sum -/
open Matrix Finset Filter
open scoped Topology
noncomputable section
namespace BTP.SemiInfinite

/-- The unshifted summand r_k(t) of the manuscript. -/
def ratioAt (a : Entries) (k t : ℕ) : ℝ :=
  cumulative a k t / cumulative a (k - 1) t

theorem normalizedTail_diagonal {p : ℕ} {a : Entries} (ha : Metelmann p a)
    {l n : ℕ} (hl : l < p) (hn : l ≤ n) : normalizedTail a p l n l = 1 := by
  rw [normalizedTail, qTail_diagonal_column ha hl hn]
  exact div_self (cumulative_pos ha hl n).ne'

theorem normalizedTail_before {p : ℕ} {a : Entries} (ha : Metelmann p a)
    {l j n : ℕ} (hjl : j < l) (hln : l ≤ n) : normalizedTail a p l n j = 0 := by
  rw [normalizedTail, qTail_column_before ha hjl hln, zero_div]

theorem adjacent_column_formula {p : ℕ} {a : Entries} (ha : Metelmann p a)
    {l : ℕ} (hl : l + 1 < p) {n : ℕ} (hn : l ≤ n) :
    qTail a p l n (l + 1) = cumulative a l n *
      ∑ s ∈ Ico (l + 1) (n + 1), ratioAt a (l + 1) s := by
  induction n, hn using Nat.le_induction with
  | base => simp [qTail, inverseEntries_upper _ _ _ _ (show l < l + 1 by omega)]
  | succ n hn ih =>
    rw [qTail_succ_row _ _ _ _ _ (by omega), qTail_diagonal_column ha hl (by omega),
      ih, cumulative_succ _ _ _ hn,
      sum_Ico_succ_top (show l + 1 ≤ n + 1 by omega)]
    simp only [ratioAt, Nat.add_sub_cancel, cumulative_succ a l n hn]
    have hc := (cumulative_pos ha (show l < p by omega) n).ne'
    have ha0 := (ha.2 l (by omega) (n + 1) (by omega)).ne'
    field_simp
    ring

theorem normalized_adjacent_column {p : ℕ} {a : Entries} (ha : Metelmann p a)
    {l : ℕ} (hl : l + 1 < p) {n : ℕ} (hn : l ≤ n) :
    normalizedTail a p l n (l + 1) =
      ∑ s ∈ Ico (l + 1) (n + 1), ratioAt a (l + 1) s := by
  rw [normalizedTail, adjacent_column_formula ha hl hn]
  exact mul_div_cancel_left₀ _ (cumulative_pos ha (by omega) n).ne'

/-- E_(k+1) with its final column k replaced by k+1. -/
def nextColumns (k : ℕ) (j : Fin (k + 1)) : ℕ := if j.val = k then k + 1 else j.val

theorem normalized_next_minor {p k : ℕ} {a : Entries} (ha : Metelmann p a)
    (hk : k + 1 < p) (n : ℕ) :
    consecutiveMinor a p (k + 1) n (nextColumns k) /
      consecutiveMinor a p (k + 1) n (fun j => j.val) =
      ∑ s ∈ Ico (k + 1) (n + k + 1), ratioAt a (k + 1) s := by
  rw [normalized_minor_identity ha (by omega)]
  let M : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
    fun i j => normalizedTail a p i.val (n + i.val) (nextColumns k j)
  change M.det = _
  have htri : M.IsUpperTriangular := by
    intro i j hji
    change j.val < i.val at hji
    change normalizedTail a p i.val (n + i.val) (nextColumns k j) = 0
    have hj : j.val ≠ k := by have := i.isLt; omega
    rw [nextColumns, ite_eq_right hj]
    exact normalizedTail_before ha hji (by omega)
  rw [Matrix.det_of_isUpperTriangular htri]
  rw [Finset.prod_eq_single (Fin.last k)]
  · change normalizedTail a p k (n + k) (nextColumns k (Fin.last k)) = _
    simp only [nextColumns, Fin.val_last]
    exact normalized_adjacent_column ha hk (by omega)
  · intro i _ hi
    have hi' : i.val ≠ k := by
      intro hv; apply hi; exact Fin.ext hv
    change normalizedTail a p i.val (n + i.val) (nextColumns k i) = 1
    rw [nextColumns, ite_eq_right hi']
    exact normalizedTail_diagonal ha (by omega) (by omega)
  · simp

/-- The index k represents order k+1; n represents row n+1. -/
def inverseMinorRatio (a : Entries) (p k n : ℕ) : ℝ :=
  consecutiveMinor a p (k + 1) (n + 1) (fun j => j.val) /
    consecutiveMinor a p (k + 1) (n + 1) (nextColumns k)

theorem adjacent_sum_shift (a : Entries) (k n : ℕ) :
    (∑ s ∈ Ico (k + 1) (n + 1 + k + 1), ratioAt a (k + 1) s) =
      partialSum (adjacentTerm a (k + 1)) n := by
  rw [sum_Ico_eq_sum_range]
  simp only [show n + 1 + k + 1 - (k + 1) = n + 1 by omega, partialSum]
  apply sum_congr rfl
  intro j _
  simp only [ratioAt, adjacentTerm, Nat.add_sub_cancel]

theorem inverseMinorRatio_eq_convergent {p k : ℕ} {a : Entries} (ha : Metelmann p a)
    (hk : k + 1 < p) (n : ℕ) :
    inverseMinorRatio a p k n = convergent (adjacentTerm a (k + 1)) n := by
  have h := normalized_next_minor ha hk (n + 1)
  rw [adjacent_sum_shift] at h
  rw [inverseMinorRatio, ← inv_div, h]
  rfl

theorem inverseMinorRatio_strictAnti {p k : ℕ} {a : Entries} (ha : Metelmann p a)
    (hk : k + 1 < p) : StrictAnti (inverseMinorRatio a p k) := by
  have h : inverseMinorRatio a p k = convergent (adjacentTerm a (k + 1)) :=
    funext (inverseMinorRatio_eq_convergent ha hk)
  rw [h]
  exact convergent_strictAnti (adjacentTerm_pos ha (by omega) hk)

theorem inverseMinorRatio_tendsto {p k : ℕ} {a : Entries} (ha : Metelmann p a)
    (hk : k + 1 < p) :
    Tendsto (inverseMinorRatio a p k) atTop (𝓝 (seriesEndpoint a (k + 1))) := by
  have h : inverseMinorRatio a p k = convergent (adjacentTerm a (k + 1)) :=
    funext (inverseMinorRatio_eq_convergent ha hk)
  rw [h]
  exact convergent_tendsto (adjacentTerm_pos ha (by omega) hk)

#print axioms inverseMinorRatio_eq_convergent
#print axioms inverseMinorRatio_tendsto
end BTP.SemiInfinite
