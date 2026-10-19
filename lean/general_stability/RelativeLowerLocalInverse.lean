import RelativeLowerCriterion

noncomputable section
open Filter
open scoped Topology
namespace BTP.RelativeStability
open BTP.GeneralStability

/-- Under the criterion, multiplication has an analytic local inverse in
both directions. Thus the nearby factor choice is unique among nearby
factor sequences, in the relative uniform norm. -/
theorem relative_lower_local_inverse (p : ℕ) (a : Fin p → ℕ → ℝ)
    (ha : ∀ i n,0<a i n) (hg : RelativeAdjacentGeometric a) :
    ∃ g : LowerBand p → FactorVariations p,
      AnalyticAt ℝ g 0 ∧ g 0=0 ∧
      (∀ᶠ E in 𝓝 (0 : LowerBand p),relativeProduct a ha (g E)=E) ∧
      (∀ᶠ h in 𝓝 (0 : FactorVariations p),g (relativeProduct a ha h)=h) ∧
      (∀ᶠ E in 𝓝 (0 : LowerBand p),
        (∀ i n,a i n/2≤relativePerturbedFactor a (g E) i n) ∧
        (∀ i n,n<p-i.val → relativePerturbedFactor a (g E) i n=a i n)) ∧
      ∃ K,∃ s ∈ 𝓝 (0 : LowerBand p),LipschitzOnWith K g s := by
  have hbij := (relativeProductDerivative_bijective_iff_adjacent p a ha).mpr hg
  let D : FactorVariations p ≃L[ℝ] LowerBand p :=
    ContinuousLinearEquiv.ofBijective (relativeProductDerivative a ha 0)
      (LinearMap.ker_eq_bot.mpr hbij.1) (LinearMap.range_eq_top.mpr hbij.2)
  have hD : HasFDerivAt (relativeProduct a ha)
      (D : FactorVariations p →L[ℝ] LowerBand p) 0 := relativeProduct_hasFDerivAt a ha 0
  obtain ⟨g,hga,hg0,hgR,hgL⟩ := BTP.AnalyticFactorization.analytic_local_inverse
    (analytic_relativeProduct a ha 0) D hD
  simp only [relativeProduct_zero] at hga hg0 hgR
  have hlim : Tendsto g (𝓝 (0 : LowerBand p)) (𝓝 0) := by
    simpa only [ContinuousAt,hg0] using hga.continuousAt
  have hsmall : ∀ᶠ E in 𝓝 (0 : LowerBand p),‖g E‖<1/2 := by
    simpa only [Metric.mem_ball,dist_zero_right] using
      hlim.eventually (Metric.ball_mem_nhds (0 : FactorVariations p) (by norm_num : (0:ℝ)<1/2))
  refine ⟨g,hga,hg0,hgR,hgL,?_,hga.hasStrictFDerivAt.exists_lipschitzOnWith⟩
  filter_upwards [hsmall] with E hE
  refine ⟨?_,fun i n hn=>relativePerturbedFactor_fixed a (g E) i n hn⟩
  intro i n
  have hh := (abs_le.mp (factorVariation_abs_le (g E) i n)).1
  have hhalf : (1:ℝ)/2≤1+factorVariation p i.val (g E) n := by linarith
  have hm := mul_le_mul_of_nonneg_left hhalf (le_of_lt (ha i n))
  simpa only [relativePerturbedFactor,div_eq_mul_inv,one_mul] using hm

#print axioms relative_lower_local_inverse
end BTP.RelativeStability
