import RelativePathBounds
import RelativeProduct

/-! A positive finite factor list may be extended constantly beyond its
last index. This preserves every coefficient of the actual finite product
and turns finite same-row comparisons into global comparisons. -/

noncomputable section
namespace BTP.RelativeStability
open Finset BTP.GeneralStability

def clampRaw (c : ℕ → ℕ → ℝ) (m i n : ℕ) : ℝ := c (min i (m-1)) n

theorem clampRaw_agree (c : ℕ → ℕ → ℝ) (m i n : ℕ) (hi : i < m) :
    clampRaw c m i n = c i n := by
  unfold clampRaw
  rw [min_eq_left (by omega)]

theorem clampRaw_pos (c : ℕ → ℕ → ℝ) (m : ℕ) (hm : 0 < m)
    (hc : ∀ i < m, ∀ n, 0 < c i n) (i n : ℕ) :
    0 < clampRaw c m i n := by
  apply hc
  have := min_le_right i (m-1)
  omega

theorem clampRaw_nonneg (c : ℕ → ℕ → ℝ) (m : ℕ) (hm : 0 < m)
    (hc : ∀ i < m, ∀ n, 0 ≤ c i n) (i n : ℕ) :
    0 ≤ clampRaw c m i n := by
  apply hc
  have := min_le_right i (m-1)
  omega

theorem clampRaw_compare (c : ℕ → ℕ → ℝ) (m : ℕ) (hm : 0 < m) (K : ℝ)
    (hc : ∀ i j n, i ≤ j → j < m → c i n ≤ K*c j n)
    (i j n : ℕ) (hij : i ≤ j) :
    clampRaw c m i n ≤ K*clampRaw c m j n := by
  apply hc
  · exact min_le_min_right _ hij
  · have := min_le_right j (m-1)
    omega

theorem productCoefficients_congr_prefix (c d : ℕ → ℕ → ℝ) (k : ℕ)
    (h : ∀ i < k, ∀ n, c i n = d i n) :
    productCoefficients c k = productCoefficients d k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hp := ih (fun i hi n => h i (by omega) n)
    have hk : c k = d k := funext (h k (by omega))
    simp only [productCoefficients, hp, hk]

theorem clampRaw_productCoefficients (c : ℕ → ℕ → ℝ) (m k : ℕ) (hk : k ≤ m) :
    productCoefficients (clampRaw c m) k = productCoefficients c k := by
  apply productCoefficients_congr_prefix
  intro i hi n
  exact clampRaw_agree c m i n (by omega)

theorem clampRaw_lastPath (c : ℕ → ℕ → ℝ) (m s n : ℕ) (hs : s ≤ m) :
    lastPath (clampRaw c m) m s n = lastPath c m s n := by
  unfold lastPath
  apply prod_congr rfl
  intro i hi
  exact clampRaw_agree c m (m-s+i) (n-i) (by have := mem_range.mp hi; omega)

theorem rawCoefficient_congr_prefix (c d : ℕ → ℕ → ℝ) (k : ℕ)
    (h : ∀ i < k, ∀ n, c i n = d i n) (s n : ℕ) :
    rawCoefficient c k s n = rawCoefficient d k s n := by
  rw [rawCoefficient_matrix, rawCoefficient_matrix,
    productCoefficients_congr_prefix c d k h]

theorem clampRaw_rawCoefficient (c : ℕ → ℕ → ℝ) (m k : ℕ) (hk : k ≤ m) (s n : ℕ) :
    rawCoefficient (clampRaw c m) k s n = rawCoefficient c k s n := by
  rw [rawCoefficient_matrix, rawCoefficient_matrix, clampRaw_productCoefficients c m k hk]

end BTP.RelativeStability
