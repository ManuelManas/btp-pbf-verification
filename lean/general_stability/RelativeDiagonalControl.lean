import RelativeNormalizedFactors
import RelativeLDUScaling

noncomputable section
namespace BTP.RelativeStability
open Finset BTP.Stability BTP.Stability.BandLDU BTP.GeneralStability

def cumulativeWeight (w : ℕ → ℝ) (n : ℕ) : ℝ := blockProduct w 0 n

theorem cumulativeWeight_pos (w : ℕ → ℝ) (hw : ∀ n,0 < w n) (n : ℕ) :
    0 < cumulativeWeight w n := blockProduct_pos w hw 0 n

theorem scaled_diagonal_ratio (a b d : ℕ → ℝ) (ha : ∀ n,0 < a n)
    (hb : ∀ n,0 < b n) (hd : ∀ n,0 < d n) (s k : ℕ) :
    scaleDiagonal d (cumulativeWeight a) (cumulativeWeight b) s /
      scaleDiagonal d (cumulativeWeight a) (cumulativeWeight b) (s+k) =
      blockProduct (crossWeight a b d) s k := by
  rw [cross_product a b d (fun n => ne_of_gt (hd n))]
  simp only [scaleDiagonal,cumulativeWeight]
  rw [blockProduct_add a 0 s k,blockProduct_add b 0 s k]
  simp only [Nat.zero_add]
  field_simp [ne_of_gt (blockProduct_pos a ha 0 s),ne_of_gt (blockProduct_pos b hb 0 s),
    ne_of_gt (blockProduct_pos a ha s k),ne_of_gt (blockProduct_pos b hb s k),ne_of_gt (hd (s+k))]

theorem scaled_diagonal_row_bound (a b d : ℕ → ℝ) (ha : ∀ n,0 < a n)
    (hb : ∀ n,0 < b n) (hd : ∀ n,0 < d n) (hg : GeometricDecay (crossWeight a b d)) :
    ∃ Z : ℝ,0 ≤ Z ∧ ∀ n,
      ∑ k ∈ range (n+1),scaleDiagonal d (cumulativeWeight a) (cumulativeWeight b) k ≤
        Z*scaleDiagonal d (cumulativeWeight a) (cumulativeWeight b) n := by
  have hc : ∀ n,0 ≤ crossWeight a b d n := by
    intro n
    exact div_nonneg (mul_nonneg (mul_nonneg (ha n).le (hb n).le) (hd (n-1)).le) (hd n).le
  obtain ⟨Z,hZ⟩ := (rowSum_bounded_iff_geometric hc).mpr hg
  have hZ0 : 0 ≤ Z := le_trans (by simp [rowSum]) (hZ 0)
  refine ⟨Z,hZ0,?_⟩
  intro n
  have hdn := scaleDiagonal_pos d (cumulativeWeight a) (cumulativeWeight b) hd
    (cumulativeWeight_pos a ha) (cumulativeWeight_pos b hb) n
  apply (div_le_iff₀ hdn).mp
  rw [Finset.sum_div]
  have he : (∑ k ∈ range (n+1),
      scaleDiagonal d (cumulativeWeight a) (cumulativeWeight b) k /
        scaleDiagonal d (cumulativeWeight a) (cumulativeWeight b) n) = rowSum (crossWeight a b d) n := by
    rw [rowSum_eq_sum]
    apply sum_congr rfl
    intro k hk
    have hkn : k ≤ n := by simpa using hk
    have hh := scaled_diagonal_ratio a b d ha hb hd k (n-k)
    rwa [Nat.add_sub_of_le hkn] at hh
  rw [he]
  exact hZ n

theorem fin_sum_Iic_eq_range {N : ℕ} (d : ℕ → ℝ) (j : Fin N) :
    ∑ k ∈ Iic j,d k.val = ∑ k ∈ range (j.val+1),d k := by
  apply sum_bij (fun k _ => k.val)
  · intro k hk
    have := mem_Iic.mp hk
    exact mem_range.mpr (by omega)
  · intro k _ l _ h
    exact Fin.ext h
  · intro k hk
    have hkj := mem_range.mp hk
    refine ⟨⟨k,by omega⟩,mem_Iic.mpr (by exact Nat.le_of_lt_succ hkj),rfl⟩
  · intro k _
    rfl

#print axioms scaled_diagonal_row_bound
end BTP.RelativeStability
