import AnalyticFactorization

noncomputable section
open Filter
open scoped Topology

namespace BTP.GeneralStability

theorem initialExtension_abs_le (first : ℕ) (h : Seq) (n : ℕ) :
    |initialExtension first h n| ≤ ‖h‖ := by
  unfold initialExtension
  split_ifs
  · exact BTP.Stability.boundedSequence_abs_le h _
  · simp

/-- Uniform control of the factor entries by the norm in the factor
space, including the zero extensions used to hold initial entries fixed. -/
theorem perturbedFactors_abs_sub_le {p : ℕ} (a : Fin p → Seq)
    (h : FactorVariations p) (i : Fin p) (n : ℕ) :
    |perturbedFactors a h i n - a i n| ≤ ‖h‖ := by
  simp only [perturbedFactors, add_sub_cancel_left]
  exact (initialExtension_abs_le _ _ _).trans (norm_le_pi_norm h i)

/-- The analytic inverse of the actual multiplication map produces
positive factors of every sufficiently close lower band matrix, with
all prescribed initial entries unchanged. -/
theorem positive_fixed_local_factorization {p : ℕ} (a : Fin p → Seq)
    {α : ℝ} (hα : 0 < α) (ha : ∀ i n, 1 ≤ n → α ≤ a i n)
    (D : FactorVariations p ≃L[ℝ] LowerBand p)
    (hD : HasFDerivAt (fixedProduct a) (D : FactorVariations p →L[ℝ] LowerBand p) 0) :
    ∃ g : LowerBand p → FactorVariations p,
      AnalyticAt ℝ g (lowerProductBand a) ∧ g (lowerProductBand a) = 0 ∧
      (∀ᶠ T in 𝓝 (lowerProductBand a),
        fixedProduct a (g T) = T ∧
        (∀ i n, 1 ≤ n → 0 < perturbedFactors a (g T) i n) ∧
        (∀ i n, n < p-i.val → perturbedFactors a (g T) i n = a i n)) := by
  obtain ⟨g, hg, hg0, hright, _⟩ :=
    BTP.AnalyticFactorization.analytic_local_inverse (analytic_fixedProduct p a 0) D hD
  simp only [fixedProduct_zero] at hg hg0 hright
  have hlim : Tendsto g (𝓝 (lowerProductBand a)) (𝓝 0) := by
    simpa only [ContinuousAt, hg0] using hg.continuousAt
  have hsmall : ∀ᶠ T in 𝓝 (lowerProductBand a), ‖g T‖ < α := by
    simpa only [Metric.mem_ball, dist_zero_right] using
      hlim.eventually (Metric.ball_mem_nhds (0 : FactorVariations p) hα)
  refine ⟨g, hg, hg0, ?_⟩
  filter_upwards [hright, hsmall] with T hprod hnorm
  refine ⟨hprod, ?_, ?_⟩
  · intro i n hn
    have habs := perturbedFactors_abs_sub_le a (g T) i n
    have hlo := (abs_le.mp habs).1
    have hbase := ha i n hn
    linarith
  · intro i n hn
    simp [perturbedFactors, initialExtension, not_le.mpr hn]

/-- Analytic local sections of lower-bidiagonal multiplication are
equivalent to bounded linear right inverses of its actual derivative.
No analyticity or differentiability of multiplication is assumed here:
both come from its explicitly proved polynomial formula. -/
theorem lowerProduct_analytic_section_iff {p : ℕ} (a : Fin p → Seq) :
    (∃ g : LowerBand p → (Fin p → Seq),
      AnalyticAt ℝ g (lowerProductBand a) ∧ g (lowerProductBand a) = a ∧
      (∀ᶠ T in 𝓝 (lowerProductBand a), lowerProductBand (g T) = T)) ↔
    ∃ B : LowerBand p →L[ℝ] (Fin p → Seq),
      (fderiv ℝ (@lowerProductBand p) a).comp B = ContinuousLinearMap.id ℝ (LowerBand p) := by
  have hf := analytic_lowerProductBand p a
  constructor
  · rintro ⟨g, hg, hga, hright⟩
    exact ⟨fderiv ℝ g (lowerProductBand a),
      BTP.AnalyticFactorization.derivative_right_inverse_of_section
        hf.differentiableAt.hasFDerivAt hg.differentiableAt.hasFDerivAt hga hright⟩
  · rintro ⟨B, hB⟩
    exact BTP.AnalyticFactorization.analytic_local_section hf _ B
      hf.differentiableAt.hasFDerivAt hB

#print axioms positive_fixed_local_factorization
#print axioms lowerProduct_analytic_section_iff

end BTP.GeneralStability
