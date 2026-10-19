import CompleteResults
import SharpUniformMinors

/-! # The three parts of the current inverse-minor lemma

`k` in `next_minor_*` represents manuscript order k+1.
`n` in `inverseMinorRatio` represents manuscript row n+1.
The determinant identities themselves include row zero.
-/
open Matrix Finset Filter
open scoped Topology
noncomputable section
namespace BTP.SemiInfinite

theorem next_minor_formula {p k : ℕ} {a : Entries} (ha : Metelmann p a)
    (hk : k + 1 < p) (n : ℕ) :
    consecutiveMinor a p (k + 1) n (nextColumns k) =
      consecutiveMinor a p (k + 1) n (fun j => j.val) *
        ∑ s ∈ Ico (k + 1) (n + k + 1), ratioAt a (k + 1) s := by
  have h := normalized_next_minor ha hk n
  have hd := (leading_minor_pos ha (show k + 1 ≤ p by omega) n).ne'
  exact (div_eq_iff hd).mp h |>.trans (mul_comm _ _)

theorem next_minor_at_zero {p k : ℕ} {a : Entries} (ha : Metelmann p a)
    (hk : k + 1 < p) : consecutiveMinor a p (k + 1) 0 (nextColumns k) = 0 := by
  rw [next_minor_formula ha hk]
  simp

theorem next_minor_pos {p k : ℕ} {a : Entries} (ha : Metelmann p a)
    (hk : k + 1 < p) (n : ℕ) :
    0 < consecutiveMinor a p (k + 1) (n + 1) (nextColumns k) := by
  rw [next_minor_formula ha hk, adjacent_sum_shift]
  exact mul_pos (leading_minor_pos ha (by omega) _) 
    (partial_pos (adjacentTerm_pos ha (by omega) hk) n)

/-- Parts (1) and (2), including the zero-row boundary case. -/
theorem inverse_minors_identities_and_limits {p k : ℕ} {a : Entries}
    (ha : Metelmann p a) (hk : k + 1 < p) :
    (∀ n, consecutiveMinor a p (k + 1) n (fun j => j.val) =
      ∏ i : Fin (k + 1), cumulative a i.val (n + i.val)) ∧
    (∀ n, 0 < consecutiveMinor a p (k + 1) n (fun j => j.val)) ∧
    (∀ n, consecutiveMinor a p (k + 1) n (nextColumns k) =
      consecutiveMinor a p (k + 1) n (fun j => j.val) *
        ∑ s ∈ Ico (k + 1) (n + k + 1), ratioAt a (k + 1) s) ∧
    consecutiveMinor a p (k + 1) 0 (nextColumns k) = 0 ∧
    (∀ n, 0 < consecutiveMinor a p (k + 1) (n + 1) (nextColumns k)) ∧
    StrictAnti (inverseMinorRatio a p k) ∧
    Tendsto (inverseMinorRatio a p k) atTop (𝓝 (seriesEndpoint a (k + 1))) := by
  exact ⟨leading_minor_formula ha (by omega), leading_minor_pos ha (by omega),
    next_minor_formula ha hk, next_minor_at_zero ha hk, next_minor_pos ha hk,
    inverseMinorRatio_strictAnti ha hk, inverseMinorRatio_tendsto ha hk⟩

/-- Part (3), with exactly the maximum used in the manuscript. -/
theorem inverse_minors_uniform_bound_complete {p : ℕ} {a : Entries}
    (ha : Metelmann p a)
    (hs : ∀ h, 0 < h → h < p → Summable (adjacentTerm a h)) :
    1 ≤ manuscriptBound a p ∧
    ∀ k, k ≤ p → ∀ n (c : Fin k → ℕ), (∀ j, c j < p) →
      |consecutiveMinor a p k n c / consecutiveMinor a p k n (fun j => j.val)| ≤
        (Nat.factorial k : ℝ) * (manuscriptBound a p) ^ k := by
  exact ⟨one_le_manuscriptBound a p,
    fun _ hk n c hc => uniform_inverse_minors_sharp ha hs hk n c hc⟩

#print axioms next_minor_at_zero
#print axioms inverse_minors_identities_and_limits
#print axioms inverse_minors_uniform_bound_complete
#print axioms global_two_sided_criterion_complete
end BTP.SemiInfinite
