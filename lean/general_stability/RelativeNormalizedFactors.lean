import RelativePrefixBounds
import RelativeComparison

/-! Dividing every factor at a given row by a common positive sequence
changes every path with the same endpoints by the same multiplier. -/
noncomputable section
namespace BTP.RelativeStability
open BTP.GeneralStability BTP.Stability BTP.Stability.BandLDU

def normalizeRaw (c : ℕ → ℕ → ℝ) (w : ℕ → ℝ) (i n : ℕ) : ℝ := c i n/w n

theorem blockProduct_succ_left (w : ℕ → ℝ) (j s : ℕ) :
    blockProduct w j (s+1)=w (j+1)*blockProduct w (j+1) s := by
  rw [show s+1=1+s by omega,blockProduct_add]
  simp only [blockProduct_succ,blockProduct_zero,one_mul]

theorem normalizeRaw_rawCoefficient (c : ℕ → ℕ → ℝ) (w : ℕ → ℝ)
    (hw : ∀ n,0 < w n) (m s j : ℕ) :
    rawCoefficient (normalizeRaw c w) m s j=rawCoefficient c m s j/blockProduct w j s := by
  induction m generalizing s j with
  | zero => cases s <;> simp [rawCoefficient]
  | succ m ih =>
    cases s with
    | zero => simp [rawCoefficient]
    | succ s =>
      simp only [rawCoefficient,ih,normalizeRaw]
      rw [blockProduct_succ_left]
      field_simp [ne_of_gt (hw (j+1)),ne_of_gt (blockProduct_pos w hw (j+1) s)]

theorem blockProduct_ratio (w : ℕ → ℝ) (hw : ∀ n,0 < w n) (j s : ℕ) :
    blockProduct w j s=blockProduct w 0 (j+s)/blockProduct w 0 j := by
  rw [blockProduct_add]
  simp only [Nat.zero_add]
  field_simp [ne_of_gt (blockProduct_pos w hw 0 j)]

#print axioms normalizeRaw_rawCoefficient
end BTP.RelativeStability
