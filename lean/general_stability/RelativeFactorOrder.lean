import RelativeExtractionMap
import Lemma24

/-! Raw factor-order bridge, valid without bounds or growth hypotheses. -/
noncomputable section
namespace BTP.RelativeStability
open BTP BTP.GeneralStability

/-- Reverse the finite factor list. Entries outside that list are unused. -/
def rawReverse (c : ℕ → ℕ → ℝ) (m i n : ℕ) : ℝ := c (m-1-i) n

theorem rawReverse_reverse_prefix (c : ℕ → ℕ → ℝ) (m i n : ℕ) (hi : i<m) :
    rawReverse (rawReverse c m) m i n=c i n := by
  unfold rawReverse
  rw [show m-1-(m-1-i)=i by omega]

theorem rawReverse_head (c : ℕ → ℕ → ℝ) (m n : ℕ) :
    rawReverse c (m+1) m n=c 0 n := by simp [rawReverse]

theorem rawReverse_tail_prefix (c : ℕ → ℕ → ℝ) (m i n : ℕ) (hi : i<m) :
    rawReverse c (m+1) i n=rawReverse (fun k=>c (k+1)) m i n := by
  unfold rawReverse
  simp only [Nat.add_sub_cancel]
  congr 1
  omega

/-- The row-coefficient product and the legacy matrix-entry recursion are
the same ordered bidiagonal product, in opposite index conventions. -/
theorem productCoefficients_eq_entry_reverse (c : ℕ → ℕ → ℝ) (m s n : ℕ) :
    productCoefficients c m s n=entry (rawReverse c m) m n s := by
  induction m generalizing c s n with
  | zero => rfl
  | succ m ih =>
    cases s with
    | zero => simp
    | succ s =>
      rw [productCoefficients_head,entry,rawReverse_head]
      have he (row d : ℕ) : entry (rawReverse c (m+1)) m row d=
          entry (rawReverse (fun k=>c (k+1)) m) m row d := by
        exact entry_congr _ _ m row d (fun i hi t _=>rawReverse_tail_prefix c m i t hi)
      rw [he,he,←ih,←ih]

/-- The inverse orientation of the same exact matrix identity. -/
theorem entry_eq_productCoefficients_reverse (c : ℕ → ℕ → ℝ) (m s n : ℕ) :
    entry c m n s=productCoefficients (rawReverse c m) m s n := by
  rw [productCoefficients_eq_entry_reverse]
  exact entry_congr _ _ m n s (fun i hi t _=>(rawReverse_reverse_prefix c m i t hi).symm)

#print axioms productCoefficients_eq_entry_reverse
#print axioms entry_eq_productCoefficients_reverse
end BTP.RelativeStability
