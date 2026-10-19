import RelativeNormalizedFactors
import RelativeFactorOrder
import RelativeLDUMatrix
import ActualPBFData

noncomputable section
namespace BTP.RelativeStability
open Finset BTP BTP.GeneralStability BTP.Stability BTP.Stability.BandLDU BTP.SemiInfinite

def rawProductBand (c : ℕ → ℕ → ℝ) (m : ℕ) : Fin m → ℕ → ℝ :=
  fun r j => rawCoefficient c m (r.val+1) j

theorem rawUnitEntry_productBand (c : ℕ → ℕ → ℝ) (m i j : ℕ) :
    rawUnitEntry (rawProductBand c m) i j=
      if j ≤ i then productCoefficients c m (i-j) i else 0 := by
  unfold rawUnitEntry rawTriangular
  split_ifs with hji hz hb
  · rw [hz,productCoefficients_diagonal]
  · simp only [rawProductBand,show i-j-1+1=i-j by omega,rawCoefficient_matrix,
      Nat.add_sub_of_le hji]
  · rw [productCoefficients_band c m (i-j) i (by omega)]
  · rfl

theorem rawUnitEntry_productBand_finite (c : ℕ → ℕ → ℝ) (m N : ℕ) :
    (fun i j : Fin N => rawUnitEntry (rawProductBand c m) i.val j.val)=
      lowerProduct N (rawReverse c m) m := by
  ext i j
  rw [rawUnitEntry_productBand,lowerProduct_entry,productCoefficients_eq_entry_reverse]

theorem rawProductBand_pos (c : ℕ → ℕ → ℝ) (hc : ∀ i n,0 < c i n) (m : ℕ) :
    ∀ r j,0 < rawProductBand c m r j := by
  intro r j
  exact rawCoefficient_pos c hc m (r.val+1) j (by omega)

def normalizedLast (c : ℕ → ℕ → ℝ) (m : ℕ) := normalizeRaw c (c (m-1))

theorem normalizedLast_pos (c : ℕ → ℕ → ℝ) (hc : ∀ i n,0 < c i n)
    (m i n : ℕ) : 0 < normalizedLast c m i n := div_pos (hc _ _) (hc _ _)

theorem normalizedLast_last (c : ℕ → ℕ → ℝ) (hc : ∀ i n,0 < c i n) (m n : ℕ) :
    normalizedLast c m (m-1) n=1 := div_self (ne_of_gt (hc _ _))

theorem normalizedLast_comparison (c : ℕ → ℕ → ℝ) (hc : ∀ i n,0 < c i n)
    (m : ℕ) {K : ℝ}
    (hcomp : ∀ i j n,i ≤ j → j < m → c i n ≤ K*c j n) :
    ∀ i j n,i ≤ j → j < m → normalizedLast c m i n ≤ K*normalizedLast c m j n := by
  intro i j n hij hj
  have hh := div_le_div_of_nonneg_right (hcomp i j n hij hj) (hc (m-1) n).le
  simpa only [normalizedLast,normalizeRaw,mul_div_assoc] using hh

theorem normalized_product_prefix_bound (c : ℕ → ℕ → ℝ) (hc : ∀ i n,0 < c i n)
    (m : ℕ) (hm : 0 < m) {K : ℝ} (hK : 1 ≤ K)
    (hcomp : ∀ i j n,i ≤ j → j < m → c i n ≤ K*c j n)
    (i j k : ℕ) (hkj : k ≤ j) (hji : j ≤ i) :
    rawUnitEntry (rawProductBand (normalizedLast c m) m) i k ≤
      (2^m*K^(2*m))*rawUnitEntry (rawProductBand (normalizedLast c m) m) i j := by
  rw [rawUnitEntry_productBand,rawUnitEntry_productBand,ite_eq_left (hkj.trans hji),ite_eq_left hji]
  have hnc := normalizedLast_pos c hc m
  by_cases hb : i-k ≤ m
  · have hh := finite_product_prefix_bound (normalizedLast c m) m hm
      (fun i _ n => (hnc i n).le) K hK (normalizedLast_comparison c hc m hcomp)
      (i-j) (j-k) i (by omega) (by omega)
    have he : normalizedLast c m (m-1)=fun _ => (1 : ℝ) := funext (normalizedLast_last c hc m)
    rw [he] at hh
    simp only [blockProduct,prod_const_one,mul_one,show i-j+(j-k)=i-k by omega] at hh
    exact hh
  · rw [productCoefficients_band _ m (i-k) i (by omega)]
    exact mul_nonneg (by positivity) (productCoefficients_nonneg _ (fun i n => (hnc i n).le) _ _ _)

theorem normalized_product_uniform_bound (c : ℕ → ℕ → ℝ) (hc : ∀ i n,0 < c i n)
    (m : ℕ) (hm : 0 < m) {K : ℝ} (hK : 1 ≤ K)
    (hcomp : ∀ i j n,i ≤ j → j < m → c i n ≤ K*c j n) (i j : ℕ) :
    rawUnitEntry (rawProductBand (normalizedLast c m) m) i j ≤ 2^m*K^(2*m) := by
  by_cases hji : j ≤ i
  · have hh := normalized_product_prefix_bound c hc m hm hK hcomp i i j hji le_rfl
    simpa [rawUnitEntry,rawTriangular] using hh
  · simp [rawUnitEntry,hji]
    positivity

theorem normalized_inverse_bound (c : ℕ → ℕ → ℝ) (hc : ∀ i n,0 < c i n)
    (p : ℕ) (hg : ∀ i,i+1 < p+1 → GeometricDecay (fun n => c i n/c (i+1) n)) :
    ∃ B : ℝ,0 ≤ B ∧ ∀ N (i j : Fin N),
      |(lowerProduct N (rawReverse (normalizedLast c (p+1)) (p+1)) (p+1))⁻¹ i j| ≤ B := by
  let a := rawReverse (normalizedLast c (p+1)) (p+1)
  have ha : ∀ i ≤ p,∀ n,0 < a i n := fun i _ n => normalizedLast_pos c hc (p+1) _ n
  have hga : ∀ i < p,GeometricDecay (fun n => a (i+1) n/a i n) := by
    intro i hi
    have hh := hg (p-i-1) (by omega)
    have he : (fun n => a (i+1) n/a i n)=(fun n => c (p-i-1) n/c (p-i) n) := by
      funext n
      dsimp [a,rawReverse,normalizedLast,normalizeRaw]
      simp only [show p-(i+1)=p-i-1 by omega]
      exact div_div_div_cancel_right₀ (ne_of_gt (hc p n)) _ _
    rw [he]
    simpa only [show p-i-1+1=p-i by omega] using hh
  obtain ⟨B,hB,hbound⟩ := actual_inverse_last_factor_dominance a p ha hga
  refine ⟨B,hB,?_⟩
  intro N i j
  rw [←actualInverse_finite a (p+1) N i j,
    actualInverse_abs a (p+1) (fun k hk n _ => (ha k (by omega) n).le)]
  by_cases hji : j.val ≤ i.val
  · have hh := hbound i.val j.val hji
    have he : a 0=fun _ => (1 : ℝ) := by
      funext n
      exact normalizedLast_last c hc (p+1) n
    rw [he] at hh
    simpa only [blockProduct,prod_const_one,mul_one] using hh
  · rw [inverseEntries_upper a (p+1) i.val j.val (by omega)]
    exact hB

#print axioms normalized_inverse_bound
#print axioms normalized_product_prefix_bound
end BTP.RelativeStability
