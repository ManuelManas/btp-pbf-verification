import AnalyticLowerStability

noncomputable section
open Filter
open scoped Topology
namespace BTP.GeneralStability

/-- The fixed-data criterion also gives both local inverse identities,
with a uniform positive margin and a Lipschitz choice of factors. -/
theorem fixed_lower_local_inverse (p : ℕ) (a : Fin p → Seq)
    (α : ℝ) (hα : 0<α) (ha : ∀ i n,α≤a i n)
    (hg : ManuscriptAdjacentGeometric p a) :
    ∃ g : LowerBand p → FactorVariations p,
      AnalyticAt ℝ g (lowerProductBand a) ∧ g (lowerProductBand a)=0 ∧
      (∀ᶠ T in 𝓝 (lowerProductBand a),fixedProduct a (g T)=T) ∧
      (∀ᶠ h in 𝓝 (0 : FactorVariations p),g (fixedProduct a h)=h) ∧
      (∀ᶠ T in 𝓝 (lowerProductBand a),
        (∀ i n,α/2≤perturbedFactors a (g T) i n) ∧
        (∀ i n,n<p-i.val → perturbedFactors a (g T) i n=a i n)) ∧
      ∃ K,∃ s ∈ 𝓝 (lowerProductBand a),LipschitzOnWith K g s := by
  have hbij := (fixedProductDerivative_bijective_iff_manuscript p a α hα ha).mpr hg
  let D : FactorVariations p ≃L[ℝ] LowerBand p :=
    ContinuousLinearEquiv.ofBijective (fixedProductDerivative p a)
      (LinearMap.ker_eq_bot.mpr hbij.1) (LinearMap.range_eq_top.mpr hbij.2)
  have hD : HasFDerivAt (fixedProduct a)
      (D : FactorVariations p →L[ℝ] LowerBand p) 0 := fixedProduct_hasFDerivAt p a
  obtain ⟨g,hga,hg0,hgR,hgL⟩ := BTP.AnalyticFactorization.analytic_local_inverse
    (analytic_fixedProduct p a 0) D hD
  simp only [fixedProduct_zero] at hga hg0 hgR
  have hlim : Tendsto g (𝓝 (lowerProductBand a)) (𝓝 0) := by
    simpa only [ContinuousAt,hg0] using hga.continuousAt
  have hsmall : ∀ᶠ T in 𝓝 (lowerProductBand a),‖g T‖<α/2 := by
    simpa only [Metric.mem_ball,dist_zero_right] using
      hlim.eventually (Metric.ball_mem_nhds (0 : FactorVariations p) (by linarith : 0<α/2))
  refine ⟨g,hga,hg0,hgR,hgL,?_,hga.hasStrictFDerivAt.exists_lipschitzOnWith⟩
  filter_upwards [hsmall] with T hT
  refine ⟨?_,?_⟩
  · intro i n
    have hh := (abs_le.mp (perturbedFactors_abs_sub_le a (g T) i n)).1
    have ha0 := ha i n
    linarith
  · intro i n hn
    simp [perturbedFactors,initialExtension,not_le.mpr hn]

#print axioms fixed_lower_local_inverse
end BTP.GeneralStability
