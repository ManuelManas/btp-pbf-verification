import RelativePathBounds
import RelativeProduct

noncomputable section
namespace BTP.RelativeStability
open BTP.Stability BTP.GeneralStability

/-- Left extraction identity for the actual ordered coefficient product. -/
theorem productCoefficients_head (c : ℕ → ℕ → ℝ) (m d n : ℕ) :
    productCoefficients c (m+1) (d+1) n =
      productCoefficients (fun i=>c (i+1)) m (d+1) n +
        c 0 n*productCoefficients (fun i=>c (i+1)) m d (n-1) := by
  induction m generalizing d n with
  | zero =>
    cases d with
    | zero => simp [productCoefficients, rightBidiagonal]
    | succ d => simp [productCoefficients, rightBidiagonal]
  | succ m ih =>
    change productCoefficients c (m+1) (d+1) n+
      productCoefficients c (m+1) d n*c (m+1) (n-d) = _
    rw [ih d n]
    cases d with
    | zero => simp [productCoefficients, rightBidiagonal]; ring
    | succ d =>
      rw [ih d n]
      simp only [productCoefficients, rightBidiagonal]
      rw [show n-(d+1)=n-1-d by omega]
      ring

def extractionFirstWeight (c : ℕ → ℕ → ℝ) (hc : ∀ i n, 0<c i n)
    (m d : ℕ) : Seq :=
  ofAbsBound (fun j=>
    productCoefficients (fun i=>c (i+1)) m (d+1) (j+d+1) /
      productCoefficients c (m+1) (d+1) (j+d+1)) 1 (by
    intro j
    rw [productCoefficients_head]
    exact fraction_abs_le_one (productCoefficients_nonneg _ (fun i n=>(hc _ _).le) _ _ _)
      (mul_nonneg (hc _ _).le (productCoefficients_nonneg _ (fun i n=>(hc _ _).le) _ _ _)))

def extractionSecondWeight (c : ℕ → ℕ → ℝ) (hc : ∀ i n, 0<c i n)
    (m d : ℕ) : Seq :=
  ofAbsBound (fun j=>
    (c 0 (j+d+1)*productCoefficients (fun i=>c (i+1)) m d (j+d)) /
      productCoefficients c (m+1) (d+1) (j+d+1)) 1 (by
    intro j
    rw [productCoefficients_head, show j+d+1-1=j+d by omega]
    rw [add_comm (productCoefficients (fun i=>c (i+1)) m (d+1) (j+d+1))
      (c 0 (j+d+1)*productCoefficients (fun i=>c (i+1)) m d (j+d))]
    exact fraction_abs_le_one
      (mul_nonneg (hc _ _).le (productCoefficients_nonneg _ (fun i n=>(hc _ _).le) _ _ _))
      (productCoefficients_nonneg _ (fun i n=>(hc _ _).le) _ _ _))

/-- Actual normalized extraction derivative in relative matrix and
relative factor coordinates. Both coefficient weights lie in [0,1]. -/
def relativeExtractionDerivative (c : ℕ → ℕ → ℝ) (hc : ∀ i n, 0<c i n)
    (m : ℕ) : Seq × LowerBand m →L[ℝ] LowerBand (m+1) :=
  ContinuousLinearMap.pi (fun r=>
    (ContinuousLinearMap.mul ℝ Seq (extractionSecondWeight c hc m r.val)).comp
      ((translate (r.val+1)).comp ((zeroExtension (m+1)).comp (ContinuousLinearMap.fst ℝ Seq (LowerBand m)))) +
    (ContinuousLinearMap.mul ℝ Seq (extractionFirstWeight c hc m r.val)).comp
      ((strictCoefficientMap m (r.val+1)).comp (ContinuousLinearMap.snd ℝ Seq (LowerBand m))) +
    (ContinuousLinearMap.mul ℝ Seq (extractionSecondWeight c hc m r.val)).comp
      ((strictCoefficientMap m r.val).comp (ContinuousLinearMap.snd ℝ Seq (LowerBand m))))

/-- Convert relative band coordinates into the actual matrix variation. -/
def relativeBandVariation (c : ℕ → ℕ → ℝ) (m : ℕ) (E : LowerBand m) (s n : ℕ) : ℝ :=
  if hs : 0<s ∧ s≤m then productCoefficients c m s n * E ⟨s-1, by omega⟩ (n-s) else 0

@[simp] theorem relativeBandVariation_zero (c : ℕ → ℕ → ℝ) (m : ℕ) (E : LowerBand m) (n : ℕ) :
    relativeBandVariation c m E 0 n=0 := by simp [relativeBandVariation]

theorem relativeBandVariation_bound (c : ℕ → ℕ → ℝ) (hc : ∀ i n, 0≤c i n)
    (m : ℕ) (E : LowerBand m) (s n : ℕ) :
    |relativeBandVariation c m E s n|≤‖E‖*productCoefficients c m s n := by
  unfold relativeBandVariation
  split_ifs with hs
  · rw [abs_mul, abs_of_nonneg (productCoefficients_nonneg c hc _ _ _)]
    have hh := (boundedSequence_abs_le (E ⟨s-1, by omega⟩) (n-s)).trans
      (norm_le_pi_norm E ⟨s-1, by omega⟩)
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hh (productCoefficients_nonneg c hc _ _ _)
  · simp only [abs_zero]
    exact mul_nonneg (norm_nonneg _) (productCoefficients_nonneg c hc _ _ _)

theorem strictCoefficientMap_relative (c : ℕ → ℕ → ℝ) (m : ℕ)
    (R : LowerBand m) (s j : ℕ) :
    productCoefficients c m s (j+s)*strictCoefficientMap m s R j =
      relativeBandVariation c m R s (j+s) := by
  unfold relativeBandVariation strictCoefficientMap
  split_ifs with hs
  · simp only [ContinuousLinearMap.proj_apply, Nat.add_sub_cancel]
  · simp

theorem relativeExtractionDerivative_actual (c : ℕ → ℕ → ℝ)
    (hc : ∀ i n,0<c i n) (m : ℕ) (v : Seq × LowerBand m)
    (r : Fin (m+1)) (j : ℕ) :
    relativeExtractionDerivative c hc m v r j =
      extractionDerivative (c 0) (relativeHeadVariation c (m+1) v.1)
        (productCoefficients (fun i=>c (i+1)) m)
        (relativeBandVariation (fun i=>c (i+1)) m v.2) (r.val+1) (j+r.val+1) /
          productCoefficients c (m+1) (r.val+1) (j+r.val+1) := by
  let n := j+r.val+1
  change (c 0 n*productCoefficients (fun i=>c (i+1)) m r.val (j+r.val) /
      productCoefficients c (m+1) (r.val+1) n)*zeroExtension (m+1) v.1 n +
    (productCoefficients (fun i=>c (i+1)) m (r.val+1) n /
      productCoefficients c (m+1) (r.val+1) n)*strictCoefficientMap m (r.val+1) v.2 j +
    (c 0 n*productCoefficients (fun i=>c (i+1)) m r.val (j+r.val) /
      productCoefficients c (m+1) (r.val+1) n)*strictCoefficientMap m r.val v.2 j = _
  have hfirst := strictCoefficientMap_relative (fun i=>c (i+1)) m v.2 (r.val+1) j
  have hprev := strictCoefficientMap_relative (fun i=>c (i+1)) m v.2 r.val j
  have hhead : relativeHeadVariation c (m+1) v.1 n = c 0 n*zeroExtension (m+1) v.1 n := rfl
  simp only [show j+(r.val+1)=n by dsimp [n]; omega] at hfirst
  have hn : n-1=j+r.val := by omega
  conv_rhs => change
    (relativeHeadVariation c (m+1) v.1 n*productCoefficients (fun i=>c (i+1)) m r.val (n-1) +
      relativeBandVariation (fun i=>c (i+1)) m v.2 (r.val+1) n +
      c 0 n*relativeBandVariation (fun i=>c (i+1)) m v.2 r.val (n-1)) /
        productCoefficients c (m+1) (r.val+1) n
  rw [←hfirst, hn, ←hprev, hhead]
  ring

theorem relativeBandVariation_coordinate (c : ℕ → ℕ → ℝ) (m : ℕ)
    (E : LowerBand m) (r : Fin m) (j : ℕ) :
    relativeBandVariation c m E (r.val+1) (j+r.val+1) =
      productCoefficients c m (r.val+1) (j+r.val+1)*E r j := by
  unfold relativeBandVariation
  have hs : 0<r.val+1 ∧ r.val+1≤m := by omega
  rw [dite_eq_left hs]
  have hi : (⟨r.val+1-1, by omega⟩ : Fin m)=r := by apply Fin.ext; rfl
  rw [hi, show j+r.val+1-(r.val+1)=j by omega]

#print axioms relativeExtractionDerivative_actual
#print axioms productCoefficients_head
#print axioms relativeBandVariation_bound
end BTP.RelativeStability
