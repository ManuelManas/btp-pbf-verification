import RelativeProductInduction
import RelativeExtractionNecessity
import RelativeComparison

/-! The complete fixed-initial lower criterion in relative norms.
The base entries are arbitrary positive real functions: neither their
size nor their reciprocals are assumed uniformly bounded. -/
noncomputable section
namespace BTP.RelativeStability
open BTP.GeneralStability
open scoped Topology
set_option maxHeartbeats 1000000

theorem relative_firstExtraction_rightInverse {m : ℕ} (a : Fin (m+1) → ℕ → ℝ)
    (ha : ∀ i n,0<a i n) (hg : RelativeAdjacentGeometric a) :
    ∃ R : LowerBand (m+1) →L[ℝ] Seq × LowerBand m,
      (relativeExtractionDerivative (extendRaw a) (extendRaw_pos a ha) m).comp R=
        ContinuousLinearMap.id ℝ _ := by
  apply relativeExtraction_rightInverse_of_adjacent
  intro j hj
  have hh := hg j (by omega)
  simpa only [extendRaw,show j<m+1 by omega,show j+1<m+1 by omega,↓reduceDIte] using hh

theorem relativeProductDerivative_injective (p : ℕ) (a : Fin p → ℕ → ℝ)
    (ha : ∀ i n,0<a i n) : Function.Injective (relativeProductDerivative a ha 0) := by
  induction p with
  | zero => exact (relativeProductDerivative_zero_bijective a ha).1
  | succ m ih =>
    exact relativeProductDerivative_succ_injective a ha
      (relativeExtraction_injective (extendRaw a) (extendRaw_pos a ha) m)
      (ih (Fin.tail a) (fun i n=>ha i.succ n))

/-- The differential of the genuine matrix product is invertible in
relative supremum norms exactly under the adjacent same-row conditions. -/
theorem relativeProductDerivative_bijective_iff_adjacent (p : ℕ) (a : Fin p → ℕ → ℝ)
    (ha : ∀ i n,0<a i n) :
    Function.Bijective (relativeProductDerivative a ha 0) ↔ RelativeAdjacentGeometric a := by
  induction p with
  | zero =>
    constructor
    · intro _ i hi
      omega
    · intro _
      exact relativeProductDerivative_zero_bijective a ha
  | succ m ih =>
    have hE := relativeExtraction_injective (extendRaw a) (extendRaw_pos a ha) m
    constructor
    · intro hD
      obtain ⟨hDE,hDT⟩ := (relativeProductDerivative_succ_bijective_iff a ha hE).mp hD
      apply (relativeAdjacentGeometric_succ_iff a).mpr
      refine ⟨?_,(ih (Fin.tail a) (fun i n=>ha i.succ n)).mp hDT⟩
      intro hm
      have hh := relativeExtraction_surjective_implies_adjacent (extendRaw a)
        (extendRaw_pos a ha) m hm hDE.2
      simpa only [extendRaw,Nat.zero_lt_succ,show 1<m+1 by omega,↓reduceDIte,Fin.mk_zero] using hh
    · intro hg
      apply (relativeProductDerivative_succ_bijective_iff a ha hE).mpr
      obtain ⟨R,hR⟩ := relative_firstExtraction_rightInverse a ha hg
      refine ⟨⟨hE,?_⟩,(ih (Fin.tail a) (fun i n=>ha i.succ n)).mpr
        ((relativeAdjacentGeometric_succ_iff a).mp hg).2⟩
      intro E
      refine ⟨R E,?_⟩
      exact congrArg (fun A : LowerBand (m+1) →L[ℝ] LowerBand (m+1)=>A E) hR

theorem relativeProductDerivative_surjective_iff_adjacent (p : ℕ) (a : Fin p → ℕ → ℝ)
    (ha : ∀ i n,0<a i n) :
    Function.Surjective (relativeProductDerivative a ha 0) ↔ RelativeAdjacentGeometric a := by
  constructor
  · intro hs
    exact (relativeProductDerivative_bijective_iff_adjacent p a ha).mp
      ⟨relativeProductDerivative_injective p a ha,hs⟩
  · intro hg
    exact ((relativeProductDerivative_bijective_iff_adjacent p a ha).mpr hg).2

/-- Arbitrary-growth relative stability, in every lower bandwidth:
positive analytic factor choices with all prescribed initial entries fixed
exist if and only if the adjacent relative products decay geometrically. -/
theorem relative_positive_choice_iff_adjacent (p : ℕ) (a : Fin p → ℕ → ℝ)
    (ha : ∀ i n,0<a i n) :
    RelativePositiveAnalyticChoice a ha ↔ RelativeAdjacentGeometric a := by
  constructor
  · intro hc
    obtain ⟨R,hR⟩ := relative_positive_choice_derivative_rightInverse a ha hc
    apply (relativeProductDerivative_surjective_iff_adjacent p a ha).mp
    intro E
    refine ⟨R E,?_⟩
    exact congrArg (fun A : LowerBand p →L[ℝ] LowerBand p=>A E) hR
  · intro hg
    have hb := (relativeProductDerivative_bijective_iff_adjacent p a ha).mpr hg
    let D := ContinuousLinearEquiv.ofBijective (relativeProductDerivative a ha 0)
      (LinearMap.ker_eq_bot.mpr hb.1) (LinearMap.range_eq_top.mpr hb.2)
    exact relative_positive_choice_of_derivative_equiv a ha D rfl

/-- The same geometric assumptions give a uniform local Lipschitz bound
on all relative factor changes, while preserving the initial entries. -/
theorem relative_positive_choice_with_lipschitz_of_adjacent (p : ℕ)
    (a : Fin p → ℕ → ℝ) (ha : ∀ i n,0<a i n) (hg : RelativeAdjacentGeometric a) :
    ∃ g : LowerBand p → FactorVariations p,
      AnalyticAt ℝ g 0 ∧ g 0=0 ∧
      (∀ᶠ E in 𝓝 (0 : LowerBand p), relativeProduct a ha (g E)=E ∧
        (∀ i n,1≤n → 0<relativePerturbedFactor a (g E) i n) ∧
        (∀ i n,n<p-i.val → relativePerturbedFactor a (g E) i n=a i n)) ∧
      ∃ K,∃ s ∈ 𝓝 (0 : LowerBand p),LipschitzOnWith K g s :=
  relative_positive_choice_with_lipschitz a ha
    ((relative_positive_choice_iff_adjacent p a ha).mpr hg)

#print axioms relativeProductDerivative_injective
#print axioms relativeProductDerivative_bijective_iff_adjacent
#print axioms relative_positive_choice_iff_adjacent
#print axioms relative_positive_choice_with_lipschitz_of_adjacent

end BTP.RelativeStability
