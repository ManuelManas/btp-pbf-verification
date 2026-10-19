import WeightedShift

/-!
# Periodic factor ratios

This file proves the scalar periodic reduction used in the manuscript's
corollaries `stab:cor:periodic-general` and `stab:cor:periodic-full`.
The analytic dependence of the matrix factors is a separate theorem;
the results here identify exactly the periodic product condition.
-/

open Finset
open scoped BigOperators
noncomputable section
namespace BTP.Stability

theorem blockProduct_rotate (w : ℕ → ℝ) (s h : ℕ) :
    blockProduct w (s+1) h * w (s+1) =
      blockProduct w s h * w (s+h+1) := by
  have hleft := prod_range_succ' (fun i => w (s+i+1)) h
  have hright := prod_range_succ (fun i => w (s+i+1)) h
  have he : (∏ i ∈ range h, w (s+(i+1)+1)) = blockProduct w (s+1) h := by
    apply prod_congr rfl
    intro i _
    congr 1
    omega
  rw [he] at hleft
  simpa [blockProduct] using hleft.symm.trans hright

theorem periodic_blockProduct {w : ℕ → ℝ} {h : ℕ}
    (hw : ∀ n, 0 < w n) (hp : ∀ n, w (n+h) = w n) (s : ℕ) :
    blockProduct w s h = blockProduct w 0 h := by
  induction s with
  | zero => rfl
  | succ s ih =>
    have he := blockProduct_rotate w s h
    have ht : w (s+h+1) = w (s+1) := by
      convert hp (s+1) using 1
      congr 1
      omega
    rw [ht] at he
    exact (mul_right_cancel₀ (ne_of_gt (hw _)) he).trans ih

theorem periodic_blockProduct_mul {w : ℕ → ℝ} {h : ℕ}
    (hw : ∀ n, 0 < w n) (hp : ∀ n, w (n+h) = w n) (s k : ℕ) :
    blockProduct w s (h*k) = (blockProduct w 0 h)^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, blockProduct_add, ih,
      periodic_blockProduct hw hp (s+h*k), pow_succ]

theorem blockProduct_mul_le {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n)
    {h : ℕ} {θ : ℝ} (hθ : 0 ≤ θ)
    (hb : ∀ s, blockProduct w s h ≤ θ) (s k : ℕ) :
    blockProduct w s (h*k) ≤ θ^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, blockProduct_add, pow_succ]
    exact mul_le_mul ih (hb _) (blockProduct_nonneg hw _ _) (pow_nonneg hθ _)

/-- A uniformly contractive block exists exactly when the product over
one period is less than one. This statement uses no asymptotic assumption. -/
theorem periodic_block_contraction_iff {w : ℕ → ℝ} {h : ℕ}
    (hh : 0 < h) (hw : ∀ n, 0 < w n) (hp : ∀ n, w (n+h) = w n) :
    (∃ k : ℕ, 0 < k ∧ ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧
      ∀ s, blockProduct w s k ≤ θ) ↔ blockProduct w 0 h < 1 := by
  constructor
  · rintro ⟨k, hk, θ, hθ0, hθ1, hb⟩
    by_contra hn
    have hc : 1 ≤ blockProduct w 0 h := le_of_not_gt hn
    have ht := blockProduct_mul_le (fun n => (hw n).le) hθ0 hb 0 h
    rw [Nat.mul_comm k h, periodic_blockProduct_mul hw hp] at ht
    have hge : 1 ≤ (blockProduct w 0 h)^k := one_le_pow₀ hc
    have hlt : θ^h < 1 := pow_lt_one₀ hθ0 hθ1 (Nat.ne_of_gt hh)
    linarith
  · intro hc
    exact ⟨h, hh, blockProduct w 0 h,
      blockProduct_nonneg (fun n => (hw n).le) _ _, hc,
      fun s => (periodic_blockProduct hw hp s).le⟩

/-- The one-period product of the shifted adjacent ratio is the ratio
of the two factor products. The shift in the denominator is essential. -/
theorem periodic_adjacent_product {a b : ℕ → ℝ} {h : ℕ}
    (ha : ∀ n, 0 < a n) (hpa : ∀ n, a (n+h) = a n) :
    blockProduct (fun n => a (n+1) / b n) 0 h =
      blockProduct a 0 h / blockProduct b 0 h := by
  simp only [blockProduct, zero_add, prod_div_distrib]
  have he : (∏ i ∈ range h, a (i+1+1)) = blockProduct a 1 h := by
    apply prod_congr rfl
    intro i _
    congr 1
    omega
  rw [he, periodic_blockProduct ha hpa]
  simp [blockProduct]

/-- Strict ordering of period products is precisely the scalar block
condition for the adjacent shifted ratio. -/
theorem periodic_adjacent_contraction_iff {a b : ℕ → ℝ} {h : ℕ}
    (hh : 0 < h) (ha : ∀ n, 0 < a n) (hb : ∀ n, 0 < b n)
    (hpa : ∀ n, a (n+h) = a n) (hpb : ∀ n, b (n+h) = b n) :
    (∃ k : ℕ, 0 < k ∧ ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧
      ∀ s, blockProduct (fun n => a (n+1)/b n) s k ≤ θ) ↔
      blockProduct a 0 h < blockProduct b 0 h := by
  have hw (n : ℕ) : 0 < a (n+1)/b n := div_pos (ha _) (hb _)
  have hp (n : ℕ) : a (n+h+1)/b (n+h) = a (n+1)/b n := by
    have he : n+h+1 = (n+1)+h := by omega
    rw [he, hpa, hpb]
  rw [periodic_block_contraction_iff hh hw hp,
    periodic_adjacent_product ha hpa]
  exact div_lt_one (prod_pos fun i _ => hb _)

theorem periodic_bounded {w : ℕ → ℝ} {h : ℕ} (hh : 0 < h)
    (hw : ∀ n, 0 ≤ w n) (hp : ∀ n, w (n+h) = w n) :
    ∃ B : ℝ, ∀ n, w n ≤ B := by
  refine ⟨∑ i ∈ range h, w i, ?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < h
    · exact single_le_sum (fun i _ => hw i) (mem_range.mpr hn)
    · have he : n-h+h = n := by omega
      have hl : n-h < n := by omega
      have hp' := hp (n-h)
      rw [he] at hp'
      rw [hp']
      exact ih (n-h) hl

/-- The full scalar periodic reduction: uniform geometric decay is
equivalent to a product less than one over one period. -/
theorem periodic_geometric_iff {w : ℕ → ℝ} {h : ℕ} (hh : 0 < h)
    (hw : ∀ n, 0 < w n) (hp : ∀ n, w (n+h) = w n) :
    (∃ C ρ : ℝ, 1 ≤ C ∧ 0 < ρ ∧ ρ < 1 ∧
      ∀ s N, blockProduct w s N ≤ C*ρ^N) ↔ blockProduct w 0 h < 1 := by
  rw [geometric_iff_block_contraction (fun n => (hw n).le)
    (periodic_bounded hh (fun n => (hw n).le) hp)]
  exact periodic_block_contraction_iff hh hw hp

theorem periodic_adjacent_geometric_iff {a b : ℕ → ℝ} {h : ℕ}
    (hh : 0 < h) (ha : ∀ n, 0 < a n) (hb : ∀ n, 0 < b n)
    (hpa : ∀ n, a (n+h) = a n) (hpb : ∀ n, b (n+h) = b n) :
    (∃ C ρ : ℝ, 1 ≤ C ∧ 0 < ρ ∧ ρ < 1 ∧
      ∀ s N, blockProduct (fun n => a (n+1)/b n) s N ≤ C*ρ^N) ↔
      blockProduct a 0 h < blockProduct b 0 h := by
  have hw (n : ℕ) : 0 < a (n+1)/b n := div_pos (ha _) (hb _)
  have hp (n : ℕ) : a (n+h+1)/b (n+h) = a (n+1)/b n := by
    have he : n+h+1 = (n+1)+h := by omega
    rw [he, hpa, hpb]
  rw [periodic_geometric_iff hh hw hp, periodic_adjacent_product ha hpa]
  exact div_lt_one (prod_pos fun i _ => hb _)

#print axioms periodic_block_contraction_iff
#print axioms periodic_adjacent_product
#print axioms periodic_geometric_iff
#print axioms periodic_adjacent_geometric_iff

end BTP.Stability
