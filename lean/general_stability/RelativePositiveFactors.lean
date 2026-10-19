import RelativeProduct
import AnalyticPositiveFactors

/-! Analytic inversion and positivity in genuine relative coordinates.
The base factor entries are arbitrary positive functions of the row;
no absolute bound or positive uniform lower bound is imposed. The final
geometric criterion is deliberately not asserted in this intermediate
module: the derivative criterion still has to be connected to extraction. -/

noncomputable section
open Filter
open scoped Topology
namespace BTP.RelativeStability
open BTP.GeneralStability

def relativePerturbedFactor {p : ℕ} (a : Fin p → ℕ → ℝ)
    (h : FactorVariations p) (i : Fin p) (n : ℕ) : ℝ :=
  a i n*(1+factorVariation p i.val h n)

theorem factorVariation_entry {p : ℕ} (h : FactorVariations p) (i : Fin p) (n : ℕ) :
    factorVariation p i.val h n = initialExtension (p-i.val) (h i) n := by
  simp only [factorVariation,i.isLt,↓reduceDIte,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply,zeroExtension_apply]

theorem factorVariation_abs_le {p : ℕ} (h : FactorVariations p) (i : Fin p) (n : ℕ) :
    |factorVariation p i.val h n| ≤ ‖h‖ := by
  rw [factorVariation_entry]
  exact (initialExtension_abs_le _ _ _).trans (norm_le_pi_norm h i)

theorem relativePerturbedFactor_fixed {p : ℕ} (a : Fin p → ℕ → ℝ)
    (h : FactorVariations p) (i : Fin p) (n : ℕ) (hn : n < p-i.val) :
    relativePerturbedFactor a h i n = a i n := by
  simp [relativePerturbedFactor,factorVariation_entry,initialExtension,not_le.mpr hn]

theorem relativePerturbedFactor_relative_bound {p : ℕ} (a : Fin p → ℕ → ℝ)
    (ha : ∀ i n,0<a i n) (h : FactorVariations p) (i : Fin p) (n : ℕ) :
    |(relativePerturbedFactor a h i n-a i n)/a i n| ≤ ‖h‖ := by
  have hz : a i n≠0 := ne_of_gt (ha i n)
  have he : (relativePerturbedFactor a h i n-a i n)/a i n = factorVariation p i.val h n := by
    unfold relativePerturbedFactor
    field_simp
    ring
  rw [he]
  exact factorVariation_abs_le h i n

/-- Solving the bounded relative-coordinate equation is exactly the
entrywise factorization of the multiplicatively perturbed original
matrix, even when all the original coefficients are unbounded. -/
theorem relative_solution_actual_entry {p : ℕ} (a : Fin p → ℕ → ℝ)
    (ha : ∀ i n,0<a i n) (h : FactorVariations p) (E : LowerBand p)
    (hE : relativeProduct a ha h=E) (r : Fin p) (j : ℕ) :
    rawCoefficient (fun i n => extendRaw a i n*(1+factorVariation p i h n)) p (r.val+1) j =
      rawCoefficient (extendRaw a) p (r.val+1) j*(1+E r j) := by
  have hz := ne_of_gt (rawCoefficient_pos (extendRaw a) (extendRaw_pos a ha)
    p (r.val+1) j (by omega))
  have he := congrArg (fun X : LowerBand p => X r j) hE
  rw [relativeProduct_actual] at he
  have hh := (div_eq_iff hz).mp he
  nlinarith

/-- The perturbation and the factor choice are measured relatively to
their base entries. The base matrix and factors themselves need not be
bounded sequences. -/
def RelativePositiveAnalyticChoice {p : ℕ} (a : Fin p → ℕ → ℝ)
    (ha : ∀ i n,0<a i n) : Prop :=
  ∃ g : LowerBand p → FactorVariations p,
    AnalyticAt ℝ g 0 ∧ g 0 = 0 ∧
    (∀ᶠ E in 𝓝 (0 : LowerBand p), relativeProduct a ha (g E)=E ∧
      (∀ i n,1≤n → 0<relativePerturbedFactor a (g E) i n) ∧
      (∀ i n,n<p-i.val → relativePerturbedFactor a (g E) i n=a i n))

theorem relative_positive_choice_of_right_inverse {p : ℕ} (a : Fin p → ℕ → ℝ)
    (ha : ∀ i n,0<a i n) (R : LowerBand p →L[ℝ] FactorVariations p)
    (hR : (relativeProductDerivative a ha 0).comp R = ContinuousLinearMap.id ℝ (LowerBand p)) :
    RelativePositiveAnalyticChoice a ha := by
  obtain ⟨g,hg,hg0,hright⟩ := BTP.AnalyticFactorization.analytic_local_section
    (analytic_relativeProduct a ha 0) (relativeProductDerivative a ha 0) R
    (relativeProduct_hasFDerivAt a ha 0) hR
  simp only [relativeProduct_zero] at hg hg0 hright
  have hlim : Tendsto g (𝓝 (0 : LowerBand p)) (𝓝 0) := by
    simpa only [ContinuousAt,hg0] using hg.continuousAt
  have hsmall : ∀ᶠ E in 𝓝 (0 : LowerBand p), ‖g E‖ < 1 := by
    simpa only [Metric.mem_ball,dist_zero_right] using
      hlim.eventually (Metric.ball_mem_nhds (0 : FactorVariations p) zero_lt_one)
  refine ⟨g,hg,hg0,?_⟩
  filter_upwards [hright,hsmall] with E hprod hnorm
  refine ⟨hprod,?_,?_⟩
  · intro i n _
    have hlow := (abs_le.mp (factorVariation_abs_le (g E) i n)).1
    exact mul_pos (ha i n) (by linarith)
  · exact fun i n hn => relativePerturbedFactor_fixed a (g E) i n hn

theorem relative_positive_choice_derivative_rightInverse {p : ℕ} (a : Fin p → ℕ → ℝ)
    (ha : ∀ i n,0<a i n) (hchoice : RelativePositiveAnalyticChoice a ha) :
    ∃ R : LowerBand p →L[ℝ] FactorVariations p,
      (relativeProductDerivative a ha 0).comp R = ContinuousLinearMap.id ℝ (LowerBand p) := by
  obtain ⟨g,hg,hg0,hprod⟩ := hchoice
  have hga : g (relativeProduct a ha 0) = 0 := by simpa only [relativeProduct_zero] using hg0
  have hgd : HasFDerivAt g (fderiv ℝ g (relativeProduct a ha 0)) (relativeProduct a ha 0) := by
    simpa only [relativeProduct_zero] using hg.differentiableAt.hasFDerivAt
  have hright : ∀ᶠ E in 𝓝 (relativeProduct a ha 0), relativeProduct a ha (g E) = E := by
    simpa only [relativeProduct_zero] using hprod.mono (fun _ h => h.1)
  exact ⟨_,BTP.AnalyticFactorization.derivative_right_inverse_of_section
    (relativeProduct_hasFDerivAt a ha 0) hgd hga hright⟩

/-- An intermediate analytic criterion. Its right-hand side is not the
geometric criterion of the manuscript; that further equivalence is a
separate algebraic and bounded-inverse argument. -/
theorem relative_positive_choice_iff_derivative_rightInverse {p : ℕ} (a : Fin p → ℕ → ℝ)
    (ha : ∀ i n,0<a i n) :
    RelativePositiveAnalyticChoice a ha ↔
      ∃ R : LowerBand p →L[ℝ] FactorVariations p,
        (relativeProductDerivative a ha 0).comp R = ContinuousLinearMap.id ℝ (LowerBand p) := by
  constructor
  · exact relative_positive_choice_derivative_rightInverse a ha
  · rintro ⟨R,hR⟩
    exact relative_positive_choice_of_right_inverse a ha R hR

theorem relative_positive_choice_with_lipschitz {p : ℕ} (a : Fin p → ℕ → ℝ)
    (ha : ∀ i n,0<a i n) (hchoice : RelativePositiveAnalyticChoice a ha) :
    ∃ g : LowerBand p → FactorVariations p,
      AnalyticAt ℝ g 0 ∧ g 0 = 0 ∧
      (∀ᶠ E in 𝓝 (0 : LowerBand p), relativeProduct a ha (g E)=E ∧
        (∀ i n,1≤n → 0<relativePerturbedFactor a (g E) i n) ∧
        (∀ i n,n<p-i.val → relativePerturbedFactor a (g E) i n=a i n)) ∧
      ∃ K, ∃ s ∈ 𝓝 (0 : LowerBand p), LipschitzOnWith K g s := by
  obtain ⟨g,hg,hg0,hprod⟩ := hchoice
  exact ⟨g,hg,hg0,hprod,hg.hasStrictFDerivAt.exists_lipschitzOnWith⟩

theorem relative_positive_choice_of_derivative_equiv {p : ℕ} (a : Fin p → ℕ → ℝ)
    (ha : ∀ i n,0<a i n) (D : FactorVariations p ≃L[ℝ] LowerBand p)
    (hD : (D : FactorVariations p →L[ℝ] LowerBand p)=relativeProductDerivative a ha 0) :
    RelativePositiveAnalyticChoice a ha := by
  apply relative_positive_choice_of_right_inverse a ha (D.symm : LowerBand p →L[ℝ] FactorVariations p)
  rw [←hD]
  apply ContinuousLinearMap.ext
  intro E
  exact D.apply_symm_apply E

#print axioms relative_positive_choice_iff_derivative_rightInverse
#print axioms relative_positive_choice_with_lipschitz
#print axioms relative_positive_choice_of_derivative_equiv

end BTP.RelativeStability
