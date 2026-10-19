import RelativeClamp
import RelativeRowSums

/-! Positive path comparisons needed to bound the relative LDU inverse.
The estimates compare only entries at the same row. -/
noncomputable section
namespace BTP.RelativeStability
open Finset BTP.GeneralStability BTP.Stability

/-- The last-factor path from row n down s steps. -/
def lastChain (c : ℕ → ℕ → ℝ) (m s n : ℕ) : ℝ :=
  ∏ t ∈ range s, c (m-1) (n-t)

theorem lastChain_nonneg (c : ℕ → ℕ → ℝ) (hc : ∀ i n, 0 ≤ c i n)
    (m s n : ℕ) : 0 ≤ lastChain c m s n := prod_nonneg (fun _ _ => hc _ _)

theorem lastPath_split (c : ℕ → ℕ → ℝ) (m r s n : ℕ) (h : r+s ≤ m) :
    lastPath c m (r+s) n =
      (∏ t ∈ range r, c (m-r-s+t) (n-t)) * lastPath c m s (n-r) := by
  unfold lastPath
  rw [prod_range_add]
  congr 1
  · apply prod_congr rfl
    intro t _
    congr 1; omega
  · apply prod_congr rfl
    intro t _
    congr 1 <;> omega

theorem lastPath_le_lastChain (c : ℕ → ℕ → ℝ)
    (hc : ∀ i n, 0 ≤ c i n) (K : ℝ) (_hK : 0 ≤ K)
    (hcomp : ∀ i j n, i ≤ j → c i n ≤ K*c j n)
    (m s n : ℕ) (hs : s ≤ m) :
    lastPath c m s n ≤ K^s*lastChain c m s n := by
  have hp : (∏ t ∈ range s, c (m-s+t) (n-t)) ≤
      ∏ t ∈ range s, K*c (m-1) (n-t) := by
    apply prod_le_prod
    · intro t _
      exact hc _ _
    · intro t ht
      exact hcomp _ _ _ (by have := mem_range.mp ht; omega)
  simpa only [prod_mul_distrib, prod_const, card_range, lastPath, lastChain] using hp

theorem lastPath_prefix_bound (c : ℕ → ℕ → ℝ)
    (hc : ∀ i n, 0 ≤ c i n) (K : ℝ) (hK : 0 ≤ K)
    (hcomp : ∀ i j n, i ≤ j → c i n ≤ K*c j n)
    (m r s n : ℕ) (h : r+s ≤ m) :
    lastPath c m (r+s) n ≤ K^(r+s)*lastPath c m r n*lastChain c m s (n-r) := by
  rw [lastPath_split c m r s n h]
  have hp : (∏ t ∈ range r, c (m-r-s+t) (n-t)) ≤ K^r*lastPath c m r n := by
    have hh : (∏ t ∈ range r, c (m-r-s+t) (n-t)) ≤
        ∏ t ∈ range r, K*c (m-r+t) (n-t) := by
      apply prod_le_prod
      · intro t _
        exact hc _ _
      · intro t _
        exact hcomp _ _ _ (by omega)
    simpa only [prod_mul_distrib, prod_const, card_range, lastPath] using hh
  have hs := lastPath_le_lastChain c hc K hK hcomp m s (n-r) (by omega)
  calc
    _ ≤ (K^r*lastPath c m r n)*(K^s*lastChain c m s (n-r)) :=
      mul_le_mul hp hs (lastPath_nonneg c hc _ _ _)
        (mul_nonneg (pow_nonneg hK _) (lastPath_nonneg c hc _ _ _))
    _ = _ := by rw [pow_add]; ring

/-- A coefficient is bounded by a shallower coefficient in the same
row times the last-factor chain joining their column indices. -/
theorem productCoefficients_prefix_bound (c : ℕ → ℕ → ℝ)
    (hc : ∀ i n, 0 ≤ c i n) (K : ℝ) (hK : 1 ≤ K)
    (hcomp : ∀ i j n, i ≤ j → c i n ≤ K*c j n)
    (m r s n : ℕ) (h : r+s ≤ m) :
    productCoefficients c m (r+s) n ≤
      2^m*K^(2*m)*productCoefficients c m r n*lastChain c m s (n-r) := by
  have hK0 : 0 ≤ K := by linarith
  have h1 := productCoefficients_le_lastPath c hc K hK hcomp m m (r+s) n le_rfl h
  have h2 := lastPath_prefix_bound c hc K hK0 hcomp m r s n h
  have h3 := lastPath_le_productCoefficients c hc m r n (by omega)
  have hpow : K^(2*(r+s)) ≤ K^(2*m) := by
    exact pow_le_pow_right₀ hK (by omega)
  calc
    _ ≤ 2^m*K^(r+s)*lastPath c m (r+s) n := h1
    _ ≤ 2^m*K^(r+s)*(K^(r+s)*lastPath c m r n*lastChain c m s (n-r)) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 2^m*K^(2*(r+s))*lastPath c m r n*lastChain c m s (n-r) := by
      rw [show 2*(r+s)=(r+s)+(r+s) by omega, pow_add]; ring
    _ ≤ 2^m*K^(2*m)*productCoefficients c m r n*lastChain c m s (n-r) := by
      apply mul_le_mul_of_nonneg_right _ (lastChain_nonneg c hc _ _ _)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hpow (by positivity)) h3
        (lastPath_nonneg c hc _ _ _) (by positivity)


theorem lastChain_blockProduct (c : ℕ → ℕ → ℝ) (m s n : ℕ) (hs : s ≤ n) :
    lastChain c m s n = blockProduct (c (m-1)) (n-s) s := by
  unfold lastChain blockProduct
  rw [← prod_range_reflect (fun t => c (m-1) (n-s+t+1)) s]
  apply prod_congr rfl
  intro t ht
  congr 1
  have := mem_range.mp ht
  omega

/-- Finite-list form: entries outside the factor list play no role. -/
theorem finite_product_prefix_bound (c : ℕ → ℕ → ℝ) (m : ℕ) (hm : 0 < m)
    (hc : ∀ i < m, ∀ n, 0 ≤ c i n) (K : ℝ) (hK : 1 ≤ K)
    (hcomp : ∀ i j n, i ≤ j → j < m → c i n ≤ K*c j n)
    (r s n : ℕ) (h : r+s ≤ m) (hn : r+s ≤ n) :
    productCoefficients c m (r+s) n ≤
      2^m*K^(2*m)*productCoefficients c m r n*
        blockProduct (c (m-1)) (n-r-s) s := by
  have hh := productCoefficients_prefix_bound (clampRaw c m)
    (clampRaw_nonneg c m hm hc) K hK (clampRaw_compare c m hm K hcomp) m r s n h
  rw [clampRaw_productCoefficients c m m le_rfl] at hh
  rw [lastChain_blockProduct _ m s (n-r) (by omega)] at hh
  have he : (clampRaw c m (m-1))=c (m-1) := by
    funext t
    exact clampRaw_agree c m (m-1) t (by omega)
  rw [he] at hh
  exact hh

#print axioms finite_product_prefix_bound
#print axioms productCoefficients_prefix_bound
end BTP.RelativeStability
