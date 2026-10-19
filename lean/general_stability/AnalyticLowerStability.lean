import LowerGeneralCriterion
import AnalyticPositiveFactors

/-! The complete fixed-initial-entry lower-band criterion. The map is the
actual product of bounded lower bidiagonal sequences, its derivative was
computed explicitly, and its invertibility is characterized by adjacent
geometric decay. The dummy value a_i(0) does not enter any matrix entry;
it is chosen positive in this encoding. -/

noncomputable section
open Filter
open scoped Topology
namespace BTP.GeneralStability

/-- A local real-analytic positive choice of factors with all initial
entries fixed, expressed in the genuine uniform factor and band norms. -/
def FixedPositiveAnalyticChoice {p : ℕ} (a : Fin p → Seq) : Prop :=
  ∃ g : LowerBand p → FactorVariations p,
    AnalyticAt ℝ g (lowerProductBand a) ∧ g (lowerProductBand a) = 0 ∧
    (∀ᶠ T in 𝓝 (lowerProductBand a),
      fixedProduct a (g T) = T ∧
      (∀ i n, 1 ≤ n → 0 < perturbedFactors a (g T) i n) ∧
      (∀ i n, n < p-i.val → perturbedFactors a (g T) i n = a i n))

/-- Main arbitrary lower-band fixed-data stability equivalence.
Neither inverse derivatives nor existence of the factorization map are
assumed: they are obtained from the scalar geometric criterion. -/
theorem fixed_initial_positive_factorization_iff_adjacent (p : ℕ) (a : Fin p → Seq)
    (α : ℝ) (hα : 0 < α) (ha : ∀ i n, α ≤ a i n) :
    FixedPositiveAnalyticChoice a ↔ AdjacentGeometric p a := by
  constructor
  · rintro ⟨g,hg,hg0,hchoice⟩
    have hright : ∀ᶠ T in 𝓝 (fixedProduct a 0), fixedProduct a (g T) = T := by
      simpa only [fixedProduct_zero] using hchoice.mono (fun _ h => h.1)
    have hga : g (fixedProduct a 0) = 0 := by simpa only [fixedProduct_zero] using hg0
    have hgd : HasFDerivAt g (fderiv ℝ g (fixedProduct a 0)) (fixedProduct a 0) :=
      (by simpa only [fixedProduct_zero] using hg.differentiableAt.hasFDerivAt)
    have hid := BTP.AnalyticFactorization.derivative_right_inverse_of_section
      (fixedProduct_hasFDerivAt p a) hgd hga hright
    have hinj : Function.Injective (fixedProductDerivative p a) :=
      fixedProductDerivative_injective p a
        (fun i n => ne_of_gt (lt_of_lt_of_le hα (ha i n)))
    have hsurj : Function.Surjective (fixedProductDerivative p a) := by
      intro E
      refine ⟨fderiv ℝ g (fixedProduct a 0) E, ?_⟩
      exact congrArg (fun A : LowerBand p →L[ℝ] LowerBand p => A E) hid
    exact (fixedProductDerivative_bijective_iff_adjacent p a α hα ha).mp ⟨hinj,hsurj⟩
  · intro hgeom
    have hbij := (fixedProductDerivative_bijective_iff_adjacent p a α hα ha).mpr hgeom
    let D : FactorVariations p ≃L[ℝ] LowerBand p :=
      ContinuousLinearEquiv.ofBijective (fixedProductDerivative p a)
        (LinearMap.ker_eq_bot.mpr hbij.1) (LinearMap.range_eq_top.mpr hbij.2)
    have hD : HasFDerivAt (fixedProduct a) (D : FactorVariations p →L[ℝ] LowerBand p) 0 := by
      convert fixedProduct_hasFDerivAt p a using 1
      rfl
    exact positive_fixed_local_factorization a hα (fun i n _ => ha i n) D hD

theorem fixed_initial_positive_factorization_iff_pairs (p : ℕ) (a : Fin p → Seq)
    (α : ℝ) (hα : 0 < α) (ha : ∀ i n, α ≤ a i n) :
    FixedPositiveAnalyticChoice a ↔ PairGeometric p a := by
  rw [fixed_initial_positive_factorization_iff_adjacent p a α hα ha,
    pairGeometric_iff_adjacent a (fun i n => lt_of_lt_of_le hα (ha i n))]

/-- The final criterion with precisely the manuscript's adjacent weights
a_i(n)/a_{i+1}(n-1), rather than the shifted extraction coordinates. -/
theorem fixed_initial_positive_factorization_iff_manuscript (p : ℕ) (a : Fin p → Seq)
    (α : ℝ) (hα : 0 < α) (ha : ∀ i n, α ≤ a i n) :
    FixedPositiveAnalyticChoice a ↔ ManuscriptAdjacentGeometric p a := by
  rw [fixed_initial_positive_factorization_iff_adjacent p a α hα ha,
    adjacentGeometric_iff_manuscript p a (fun i n => lt_of_lt_of_le hα (ha i n))]

theorem fixed_positive_choice_with_lipschitz (p : ℕ) (a : Fin p → Seq)
    (α : ℝ) (hα : 0 < α) (ha : ∀ i n, α ≤ a i n)
    (hgeom : ManuscriptAdjacentGeometric p a) :
    ∃ g : LowerBand p → FactorVariations p,
      AnalyticAt ℝ g (lowerProductBand a) ∧ g (lowerProductBand a) = 0 ∧
      (∀ᶠ T in 𝓝 (lowerProductBand a), fixedProduct a (g T) = T ∧
        (∀ i n, 1 ≤ n → 0 < perturbedFactors a (g T) i n) ∧
        (∀ i n, n < p-i.val → perturbedFactors a (g T) i n = a i n)) ∧
      ∃ K, ∃ s ∈ 𝓝 (lowerProductBand a), LipschitzOnWith K g s := by
  obtain ⟨g,hg,hg0,hchoice⟩ :=
    (fixed_initial_positive_factorization_iff_manuscript p a α hα ha).mpr hgeom
  exact ⟨g,hg,hg0,hchoice,hg.hasStrictFDerivAt.exists_lipschitzOnWith⟩

#print axioms fixed_initial_positive_factorization_iff_adjacent
#print axioms fixed_initial_positive_factorization_iff_pairs
#print axioms fixed_initial_positive_factorization_iff_manuscript
#print axioms fixed_positive_choice_with_lipschitz

end BTP.GeneralStability
