import RelativeExtractionInverse

noncomputable section
namespace BTP.RelativeStability
open BTP.Stability BTP.GeneralStability
set_option maxHeartbeats 2000000

theorem relative_extraction_equation (c : ℕ → ℕ → ℝ) (hc : ∀ i n,0<c i n)
    (m : ℕ) (v : Seq × LowerBand m) (E : LowerBand (m+1))
    (he : relativeExtractionDerivative c hc m v=E)
    (s n : ℕ) (hs : 0<s ∧ s≤m+1) (hn : s≤n) :
    extractionDerivative (c 0) (relativeHeadVariation c (m+1) v.1)
      (productCoefficients (fun i=>c (i+1)) m)
      (relativeBandVariation (fun i=>c (i+1)) m v.2) s n =
      relativeBandVariation c (m+1) E s n := by
  let r : Fin (m+1) := ⟨s-1, by omega⟩
  have hrs : r.val+1=s := by dsimp [r]; omega
  have hrn : n-s+r.val+1=n := by dsimp [r]; omega
  have hh := congrArg (fun F : LowerBand (m+1)=>F r (n-s)) he
  rw [relativeExtractionDerivative_actual, hrn, hrs] at hh
  have hp := ne_of_gt (productCoefficients_pos c hc (m+1) s n hs.2)
  have hb := relativeBandVariation_coordinate c (m+1) E r (n-s)
  rw [hrn, hrs] at hb
  rw [hb]
  exact (div_eq_iff hp).mp hh |>.trans (mul_comm _ _)

theorem eliminate_congr_valid (a : ℕ → ℝ) (E F : RowCoefficients)
    (k n : ℕ) (hn : k≤n)
    (he : ∀ s row, 0<s → s≤k → s≤row → E s row=F s row) :
    eliminate a E k n=eliminate a F k n := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    simp only [eliminate]
    rw [he (k+1) n (by omega) (le_refl _) hn,
      ih (n-1) (by omega) (fun s row hs hsk hsr=>he s row hs (by omega) hsr)]

theorem relative_extraction_elimination (c : ℕ → ℕ → ℝ) (hc : ∀ i n,0<c i n)
    (m : ℕ) (v : Seq × LowerBand m) (E : LowerBand (m+1))
    (he : relativeExtractionDerivative c hc m v=E) (n : ℕ) (hn : m+1≤n) :
    scalarResidual (c 0) (relativeHeadVariation c (m+1) v.1)
      (productCoefficients (fun i=>c (i+1)) m) m n =
        eliminate (c 0) (relativeBandVariation c (m+1) E) (m+1) n := by
  have hh := eliminate_congr_valid (c 0)
    (extractionDerivative (c 0) (relativeHeadVariation c (m+1) v.1)
      (productCoefficients (fun i=>c (i+1)) m)
      (relativeBandVariation (fun i=>c (i+1)) m v.2))
    (relativeBandVariation c (m+1) E) (m+1) n hn
    (fun s row hs hsm hsr=>relative_extraction_equation c hc m v E he s row ⟨hs,hsm⟩ hsr)
  rw [eliminate_extractionDerivative _ _ _ _ (fun n=>relativeBandVariation_zero _ _ _ n)] at hh
  have ht : relativeBandVariation (fun i=>c (i+1)) m v.2 (m+1) n=0 := by
    simp [relativeBandVariation]
  rw [ht, add_zero] at hh
  exact hh

theorem relativeBandVariation_zero_data (c : ℕ → ℕ → ℝ) (m s n : ℕ) :
    relativeBandVariation c m 0 s n=0 := by
  unfold relativeBandVariation
  split_ifs <;> simp

theorem eliminate_zero (a : ℕ → ℝ) (k n : ℕ) : eliminate a (fun _ _=>0) k n=0 := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [eliminate, ih]

theorem rawDifferenceProduct_zero (w : ℕ → ℕ → ℝ) (k : ℕ) :
    rawDifferenceProduct w k (fun _=>0)=fun _=>0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [rawDifferenceProduct, ih]
    funext n
    cases n <;> simp [differenceFun]

theorem rawDifferenceProduct_injective (w : ℕ → ℕ → ℝ) (k : ℕ) :
    Function.Injective (rawDifferenceProduct w k) := by
  intro f g h
  have hh := congrArg (rawSolutionProduct w k) h
  simpa only [rawSolution_difference] using hh

theorem relativeExtraction_kernel (c : ℕ → ℕ → ℝ) (hc : ∀ i n,0<c i n)
    (m : ℕ) (v : Seq × LowerBand m)
    (he : relativeExtractionDerivative c hc m v=0) : v=0 := by
  have hx : v.1=0 := by
    apply BoundedContinuousFunction.ext
    intro n
    have hd : rawDifferenceProduct (extractionWeight c (m+1)) m v.1=fun _=>0 := by
      funext n
      have hh := relative_extraction_elimination c hc m v 0 he (n+(m+1)) (by omega)
      have hz : relativeBandVariation c (m+1) 0=fun _ _=>0 := by
        funext s n
        exact relativeBandVariation_zero_data c _ s n
      rw [hz, eliminate_zero] at hh
      have hn := normalized_residual_eq c hc (m+1) (by omega) v.1 m n
      rw [hh, zero_div] at hn
      exact hn.symm
    have hz := rawDifferenceProduct_zero (extractionWeight c (m+1)) m
    have hh := rawDifferenceProduct_injective (extractionWeight c (m+1)) m (hd.trans hz.symm)
    exact congrFun hh n
  have hr (s n : ℕ) (hs : s≤m) (hn : s≤n) :
      relativeBandVariation (fun i=>c (i+1)) m v.2 s n=0 := by
    induction s generalizing n with
    | zero => exact relativeBandVariation_zero _ _ _ _
    | succ s ih =>
      have hh := relative_extraction_equation c hc m v 0 he (s+1) n ⟨by omega,by omega⟩ hn
      have hz : relativeHeadVariation c (m+1) v.1 n=0 := by rw [hx]; simp [relativeHeadVariation]
      change relativeHeadVariation c (m+1) v.1 n*productCoefficients (fun i=>c (i+1)) m s (n-1)+
        relativeBandVariation (fun i=>c (i+1)) m v.2 (s+1) n+
        c 0 n*relativeBandVariation (fun i=>c (i+1)) m v.2 s (n-1) = _ at hh
      rw [hz, ih (n-1) (by omega) (by omega), relativeBandVariation_zero_data] at hh
      simpa using hh
  apply Prod.ext hx
  funext r
  apply BoundedContinuousFunction.ext
  intro j
  have hh := hr (r.val+1) (j+r.val+1) (by omega) (by omega)
  rw [relativeBandVariation_coordinate] at hh
  exact (mul_eq_zero.mp hh).resolve_left
    (ne_of_gt (productCoefficients_pos (fun i=>c (i+1)) (fun i n=>hc (i+1) n) _ _ _ (by omega)))

/-- Uniqueness of relative extraction with the prescribed initial rows,
without any growth or decay assumption. -/
theorem relativeExtraction_injective (c : ℕ → ℕ → ℝ) (hc : ∀ i n,0<c i n) (m : ℕ) :
    Function.Injective (relativeExtractionDerivative c hc m) := by
  intro v w he
  apply sub_eq_zero.mp
  apply relativeExtraction_kernel c hc m (v-w)
  rw [map_sub, he, sub_self]

theorem productCoefficients_deepest (c : ℕ → ℕ → ℝ) (m n : ℕ) :
    productCoefficients c m m n=lastPath c m m n := by
  induction m generalizing n with
  | zero => simp [productCoefficients]
  | succ m ih =>
    change productCoefficients c m (m+1) n+productCoefficients c m m n*c m (n-m)=_
    rw [productCoefficients_band _ _ _ _ (by omega), zero_add, ih,
      lastPath_succ_right c (m+1) m n (by omega)]
    simp

theorem eliminate_relative_deepest (c : ℕ → ℕ → ℝ) (m n : ℕ) :
    eliminate (c 0) (relativeBandVariation c (m+1) (deepestBand m 1)) (m+1) n=
      scale c m n := by
  have hz (s row : ℕ) (hs : s≤m) : relativeBandVariation c (m+1) (deepestBand m 1) s row=0 := by
    unfold relativeBandVariation
    split_ifs with hh
    · simp [deepestBand, show s-1≠m by omega]
    · rfl
  have hel (s row : ℕ) (hs : s≤m) : eliminate (c 0)
      (relativeBandVariation c (m+1) (deepestBand m 1)) s row=0 := by
    induction s generalizing row with
    | zero => rfl
    | succ s ih => simp [eliminate, hz _ _ hs, ih (row-1) (by omega)]
  rw [eliminate, hel m (n-1) (le_refl _), mul_zero, sub_zero]
  simp only [relativeBandVariation, show 0<m+1 ∧ m+1≤m+1 by omega,
    deepestBand, Nat.add_sub_cancel]
  change productCoefficients c (m+1) (m+1) n*1=scale c m n
  rw [mul_one, productCoefficients_deepest, lastPath_all_eq_scale]

/-- Necessity of the first adjacent same-row condition from actual
surjectivity of relative matrix extraction, with no assumed bound on entries. -/
theorem relativeExtraction_surjective_implies_adjacent (c : ℕ → ℕ → ℝ)
    (hc : ∀ i n,0<c i n) (m : ℕ) (hm : 0<m)
    (hs : Function.Surjective (relativeExtractionDerivative c hc m)) :
    GeometricDecay (fun n=>c 0 n/c 1 n) := by
  obtain ⟨v,hv⟩ := hs (deepestBand m 1)
  apply adjacent_geometric_of_normalized_residual c hc (m+1) (by omega) v.1
  intro n
  have hh := relative_extraction_elimination c hc m v (deepestBand m 1) hv (n+(m+1)) (by omega)
  rw [eliminate_relative_deepest] at hh
  rw [show m+1-1=m by omega, hh]
  exact div_self (ne_of_gt (scale_pos c hc _ _))

#print axioms relativeExtraction_injective
#print axioms relativeExtraction_surjective_implies_adjacent
end BTP.RelativeStability
