import UniformMinors

/-! # The explicit uniform constant in Lemma `global-inverse-minors`

The proof follows the manuscript: bound each nested sum by the product
of its adjacent series, take the maximum of the finitely many products
and 1, and expand the normalized determinant.
-/
open Matrix Finset
noncomputable section
namespace BTP.SemiInfinite

/-- The positive adjacent Metelmann series S_k, when summable. -/
def adjacentSeries (a : Entries) (k : ℕ) : ℝ := ∑' n, adjacentTerm a k n

/-- Product S_(l+1) ... S_j; the diagonal case l=j has value 1. -/
def consecutiveSeriesProduct (a : Entries) (l j : ℕ) : ℝ :=
  ∏ h ∈ Ico (l + 1) (j + 1), adjacentSeries a h

/-- Exactly the finite set displayed in the definition of mathfrak B. -/
def manuscriptBoundValues (a : Entries) (p : ℕ) : Finset ℝ := by
  classical
  exact insert 1 (((range p ×ˢ range p).filter (fun ij => ij.1 < ij.2)).image
    (fun ij => consecutiveSeriesProduct a ij.1 ij.2))

theorem manuscriptBoundValues_nonempty (a : Entries) (p : ℕ) :
    (manuscriptBoundValues a p).Nonempty := by
  classical
  exact ⟨1, by simp [manuscriptBoundValues]⟩

/-- The manuscript's constant, including B=1 when p=1. -/
def manuscriptBound (a : Entries) (p : ℕ) : ℝ :=
  (manuscriptBoundValues a p).max' (manuscriptBoundValues_nonempty a p)

theorem one_le_manuscriptBound (a : Entries) (p : ℕ) :
    1 ≤ manuscriptBound a p := by
  classical
  exact Finset.le_max' _ _ (by simp [manuscriptBoundValues])

theorem consecutiveSeriesProduct_le_manuscriptBound (a : Entries)
    {p l j : ℕ} (hlj : l < j) (hj : j < p) :
    consecutiveSeriesProduct a l j ≤ manuscriptBound a p := by
  classical
  apply Finset.le_max'
  apply mem_insert_of_mem
  apply mem_image.mpr
  refine ⟨(l,j), ?_, rfl⟩
  simp only [mem_filter, mem_product, mem_range]
  exact ⟨⟨by omega, hj⟩, hlj⟩

theorem manuscriptBound_one (a : Entries) : manuscriptBound a 1 = 1 := by
  classical
  simp [manuscriptBound, manuscriptBoundValues, Finset.range_one,
    Finset.filter_singleton]

theorem consecutiveSeriesProduct_nonneg {p : ℕ} {a : Entries}
    (ha : Metelmann p a)
    (hs : ∀ k, 0 < k → k < p → Summable (adjacentTerm a k))
    {l j : ℕ} (hj : j < p) : 0 ≤ consecutiveSeriesProduct a l j := by
  apply prod_nonneg
  intro h hh
  have hbounds := mem_Ico.mp hh
  exact ((hs h (by omega) (by omega)).tsum_pos
    (fun n => (adjacentTerm_pos ha (by omega) (by omega) n).le) 0
    (adjacentTerm_pos ha (by omega) (by omega) 0)).le

private theorem adjacent_partial_le_series {p : ℕ} {a : Entries}
    (ha : Metelmann p a) {k : ℕ} (hk : 0 < k) (hkp : k < p)
    (hs : Summable (adjacentTerm a k)) (n : ℕ) :
    (∑ s ∈ Ico k (n + 1), ratioAt a k s) ≤ adjacentSeries a k := by
  rw [sum_Ico_eq_sum_range]
  change (∑ s ∈ range (n + 1 - k), adjacentTerm a k s) ≤ _
  exact Summable.sum_le_tsum _ (fun i _ => (adjacentTerm_pos ha hk hkp i).le) hs

/-- The entrywise nested-sum bound used in the manuscript, before taking a maximum. -/
theorem normalizedTail_le_consecutiveSeriesProduct {p : ℕ} {a : Entries}
    (ha : Metelmann p a)
    (hs : ∀ k, 0 < k → k < p → Summable (adjacentTerm a k))
    {l j n : ℕ} (hlj : l ≤ j) (hj : j < p) (hn : l ≤ n) :
    normalizedTail a p l n j ≤ consecutiveSeriesProduct a l j := by
  have hbound : ∀ d l, p - l = d → l < p → ∀ j, l ≤ j → j < p →
      ∀ n, l ≤ n → normalizedTail a p l n j ≤ consecutiveSeriesProduct a l j := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro l hdl hl j hlj hj n hn
      by_cases heq : l = j
      · subst j
        rw [normalizedTail_diagonal ha hl hn]
        simp [consecutiveSeriesProduct]
      · have hlt : l < j := by omega
        have hlp : l + 1 < p := by omega
        rw [normalizedTail_sum ha hlt hj hn]
        calc
          _ ≤ ∑ s ∈ Ico (l + 1) (n + 1),
              ratioAt a (l + 1) s * consecutiveSeriesProduct a (l + 1) j := by
            apply sum_le_sum
            intro s hmem
            apply mul_le_mul_of_nonneg_left
              (ih (p - (l + 1)) (by omega) (l + 1) rfl hlp j (by omega) hj s
                (mem_Ico.mp hmem).1)
            exact (div_pos (cumulative_pos ha hlp s)
              (cumulative_pos ha (by omega) s)).le
          _ = (∑ s ∈ Ico (l + 1) (n + 1), ratioAt a (l + 1) s) *
                consecutiveSeriesProduct a (l + 1) j := by rw [sum_mul]
          _ ≤ adjacentSeries a (l + 1) * consecutiveSeriesProduct a (l + 1) j :=
            mul_le_mul_of_nonneg_right
              (adjacent_partial_le_series ha (by omega) hlp (hs _ (by omega) hlp) n)
              (consecutiveSeriesProduct_nonneg ha hs hj)
          _ = consecutiveSeriesProduct a l j := by
            unfold consecutiveSeriesProduct
            exact (Finset.prod_eq_prod_Ico_succ_bot (by omega)
              (adjacentSeries a)).symm
  exact hbound (p-l) l rfl (by omega) j hlj hj n hn

theorem normalizedTail_le_manuscriptBound {p : ℕ} {a : Entries}
    (ha : Metelmann p a)
    (hs : ∀ k, 0 < k → k < p → Summable (adjacentTerm a k))
    {l j n : ℕ} (hl : l < p) (hj : j < p) (hn : l ≤ n) :
    normalizedTail a p l n j ≤ manuscriptBound a p := by
  by_cases hjl : j < l
  · rw [normalizedTail_before ha hjl hn]
    exact (by norm_num : (0:ℝ) ≤ 1).trans (one_le_manuscriptBound a p)
  · by_cases heq : j = l
    · subst j
      rw [normalizedTail_diagonal ha hl hn]
      exact one_le_manuscriptBound a p
    · exact (normalizedTail_le_consecutiveSeriesProduct ha hs (by omega) hj hn).trans
        (consecutiveSeriesProduct_le_manuscriptBound a (by omega) hj)

/-- Literal uniform-minor inequality with the explicit constant mathfrak B.
The columns may be arbitrary indices below p; in particular this includes
every increasing k-element column subset used in the manuscript. -/
theorem uniform_inverse_minors_sharp {p : ℕ} {a : Entries} (ha : Metelmann p a)
    (hs : ∀ h, 0 < h → h < p → Summable (adjacentTerm a h))
    {k : ℕ} (hk : k ≤ p) (n : ℕ) (c : Fin k → ℕ) (hc : ∀ j, c j < p) :
    |consecutiveMinor a p k n c / consecutiveMinor a p k n (fun j => j.val)| ≤
      (Nat.factorial k : ℝ) * (manuscriptBound a p) ^ k := by
  rw [normalized_minor_identity ha hk]
  apply abs_det_le_factorial _ ((by norm_num : (0:ℝ) ≤ 1).trans
    (one_le_manuscriptBound a p))
  intro i j
  rw [Matrix.of_apply, abs_of_nonneg (normalizedTail_nonneg ha (by omega) _ _)]
  exact normalizedTail_le_manuscriptBound ha hs (by omega) (hc j) (by omega)

#print axioms normalizedTail_le_consecutiveSeriesProduct
#print axioms uniform_inverse_minors_sharp
#print axioms manuscriptBound_one
end BTP.SemiInfinite
