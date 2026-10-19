import RelativeExtractionInverse
import RelativeClamp

noncomputable section
namespace BTP.RelativeStability
open Finset BTP.Stability BTP.GeneralStability
set_option maxHeartbeats 2000000

theorem geometric_uniform_bound (w : ℕ → ℝ) (hg : GeometricDecay w) :
    ∃ B : ℝ, 1≤B ∧ ∀ n, w n≤B := by
  obtain ⟨C,ρ,hC,hρ,hρ1,hbound⟩ := hg
  refine ⟨max 1 (max (w 0) C), le_max_left _ _, ?_⟩
  intro n
  cases n with
  | zero => exact (le_max_left _ _).trans (le_max_right _ _)
  | succ n =>
    have hh := hbound n 1
    simp only [blockProduct, prod_range_one, Nat.add_zero, pow_one] at hh
    have hc0 : 0≤C := by linarith
    exact hh.trans ((mul_le_of_le_one_right hc0 hρ1.le).trans
      ((le_max_right _ _).trans (le_max_right _ _)))

/-- The required finite same-row comparison follows from the length-one
case of the adjacent geometric bounds; no absolute entry bound is used. -/
theorem sameRow_finite_comparison (c : ℕ → ℕ → ℝ) (hc : ∀ i n,0<c i n)
    (m : ℕ) (hg : ∀ j, j+1<m → GeometricDecay (fun n=>c j n/c (j+1) n)) :
    ∃ K : ℝ, 1≤K ∧ ∀ i j n, i≤j → j<m → c i n≤K*c j n := by
  induction m with
  | zero => exact ⟨1,le_refl _,fun _ _ _ _ hj=>by omega⟩
  | succ m ih =>
    by_cases hm : m=0
    · subst m
      refine ⟨1,le_refl _,?_⟩
      intro i j n hij hj
      have hi : i=0 := by omega
      have hj0 : j=0 := by omega
      subst i; subst j
      simp
    · obtain ⟨K,hK,hcomp⟩ := ih (fun j hj=>hg j (by omega))
      obtain ⟨B,hB,hb⟩ := geometric_uniform_bound (fun n=>c (m-1) n/c m n) (by
        have hh := hg (m-1) (by omega)
        simpa only [show m-1+1=m by omega] using hh)
      have hlast (n : ℕ) : c (m-1) n≤B*c m n := (div_le_iff₀ (hc m n)).mp (hb n)
      have hKB : 1≤K*B := hK.trans (le_mul_of_one_le_right (by linarith) hB)
      refine ⟨K*B,hKB,?_⟩
      intro i j n hij hj
      by_cases hjm : j<m
      · exact (hcomp i j n hij hjm).trans (mul_le_mul_of_nonneg_right
          (le_mul_of_one_le_right (by linarith) hB) (hc j n).le)
      · have hj0 : j=m := by omega
        subst j
        by_cases him : i=m
        · subst i
          exact le_mul_of_one_le_left (hc m n).le hKB
        · calc
            c i n ≤ K*c (m-1) n := hcomp i (m-1) n (by omega) (by omega)
            _ ≤ K*(B*c m n) := mul_le_mul_of_nonneg_left (hlast n) (by linarith)
            _ = _ := by ring

theorem relativeExtractionDerivative_congr_prefix (c d : ℕ → ℕ → ℝ)
    (hc : ∀ i n,0<c i n) (hd : ∀ i n,0<d i n) (m : ℕ)
    (he : ∀ i<m+1, ∀ n, c i n=d i n) :
    relativeExtractionDerivative c hc m=relativeExtractionDerivative d hd m := by
  have h0 : c 0=d 0 := by funext n; exact he 0 (by omega) n
  have htail : productCoefficients (fun i=>c (i+1)) m=productCoefficients (fun i=>d (i+1)) m := by
    exact productCoefficients_congr_prefix _ _ m (fun i hi n=>he (i+1) (by omega) n)
  have hfull : productCoefficients c (m+1)=productCoefficients d (m+1) := by
    exact productCoefficients_congr_prefix _ _ _ he
  apply ContinuousLinearMap.ext
  intro v
  funext r
  apply BoundedContinuousFunction.ext
  intro j
  rw [relativeExtractionDerivative_actual, relativeExtractionDerivative_actual, hfull, htail, h0]
  have hhead : relativeHeadVariation c (m+1) v.1=relativeHeadVariation d (m+1) v.1 := by
    funext n
    unfold relativeHeadVariation
    rw [h0]
  have hR : relativeBandVariation (fun i=>c (i+1)) m v.2=
      relativeBandVariation (fun i=>d (i+1)) m v.2 := by
    funext s n
    unfold relativeBandVariation
    rw [htail]
  rw [hhead,hR]

/-- Genuine relative extraction has a bounded linear right inverse under
exactly the adjacent geometric hypotheses used in the manuscript. The
comparison constant is derived, rather than imposed. -/
theorem relativeExtraction_rightInverse_of_adjacent (c : ℕ → ℕ → ℝ)
    (hc : ∀ i n,0<c i n) (m : ℕ)
    (hg : ∀ j, j<m → GeometricDecay (fun n=>c j n/c (j+1) n)) :
    ∃ R : LowerBand (m+1) →L[ℝ] Seq × LowerBand m,
      (relativeExtractionDerivative c hc m).comp R=ContinuousLinearMap.id ℝ _ := by
  obtain ⟨K,hK,hcomp⟩ := sameRow_finite_comparison c hc (m+1) (fun j hj=>hg j (by omega))
  let d := clampRaw c (m+1)
  have hd : ∀ i n,0<d i n := clampRaw_pos c (m+1) (by omega) (fun i _ n=>hc i n)
  have hcompd : ∀ i j n, i≤j → d i n≤K*d j n :=
    clampRaw_compare c (m+1) (by omega) K hcomp
  have hgd : ∀ j, j<m → GeometricDecay (fun n=>d j n/d (j+1) n) := by
    intro j hj
    have heq : (fun n=>d j n/d (j+1) n)=(fun n=>c j n/c (j+1) n) := by
      funext n
      dsimp [d]
      rw [clampRaw_agree c (m+1) j n (by omega),clampRaw_agree c (m+1) (j+1) n (by omega)]
    rw [heq]
    exact hg j hj
  obtain ⟨R,hR⟩ := relativeExtraction_rightInverse_of_comparable d hd m K hK hcompd hgd
  refine ⟨R,?_⟩
  have heq := relativeExtractionDerivative_congr_prefix d c hd hc m
    (fun i hi n=>clampRaw_agree c (m+1) i n hi)
  rw [heq] at hR
  exact hR

#print axioms sameRow_finite_comparison
#print axioms relativeExtraction_rightInverse_of_adjacent
end BTP.RelativeStability
