import FullFreeCriterion

/-! Differentiability at the base matrix already forces the complete
full-band criterion and hence yields a real-analytic positive choice. -/
noncomputable section
open Filter Finset
open scoped Topology BigOperators
namespace BTP.GeneralStability
open BTP BTP.SemiInfinite BTP.Stability.BandLDU

def FullFreePositiveDifferentiableChoice {p q : ℕ}
    (a : Fin p → Seq) (d : Seq) (b : Fin q → Seq) : Prop :=
  ∃ g : FullBand p q → FullBand p q,
    DifferentiableAt ℝ g (lduProduct (factorBase a d b)) ∧
    g (lduProduct (factorBase a d b))=0 ∧
    (∀ᶠ T in 𝓝 (lduProduct (factorBase a d b)),
      freeFullProduct a d b (g T)=T ∧
      (∀ i n, 1≤n → 0<freePerturbedFactors a (g T).1 i n) ∧
      (∀ j n, 1≤n → 0<freePerturbedFactors b (g T).2.2 j n) ∧
      (∀ n, 0<(d+(g T).2.1) n))

theorem full_free_differentiable_rightInverse {p q : ℕ}
    (a : Fin p → Seq) (d : Seq) (b : Fin q → Seq)
    (hchoice : FullFreePositiveDifferentiableChoice a d b) :
    ∃ R : FullBand p q →L[ℝ] FullBand p q,
      (((lduProductDerivative (factorBase a d b)).comp
        (freeTriangularDerivative a b)).comp R)=ContinuousLinearMap.id ℝ (FullBand p q) := by
  obtain ⟨g,hg,hg0,hprod⟩ := hchoice
  have hga : g (freeFullProduct a d b 0)=0 := by
    simpa only [freeFullProduct_zero] using hg0
  have hgd : HasFDerivAt g (fderiv ℝ g (freeFullProduct a d b 0))
      (freeFullProduct a d b 0) := by
    simpa only [freeFullProduct_zero] using hg.hasFDerivAt
  have hright : ∀ᶠ T in 𝓝 (freeFullProduct a d b 0),freeFullProduct a d b (g T)=T := by
    simpa only [freeFullProduct_zero] using hprod.mono (fun _ h => h.1)
  exact ⟨_,BTP.AnalyticFactorization.derivative_right_inverse_of_section
    (freeFullProduct_hasFDerivAt a d b) hgd hga hright⟩

/-- A bounded right inverse of the composed derivative already controls
all joint rows of the actual signed triangular inverses. -/
theorem joint_rows_of_composed_rightInverse {p q : ℕ}
    (a : Fin p → Seq) (d : Seq) (b : Fin q → Seq) (hd : ∀ n,d n≠0)
    {M : ℝ} (hM : 0≤M) (haM : ∀ i n,|a i n|≤M) (hbM : ∀ j n,|b j n|≤M)
    (B R : FullBand p q →L[ℝ] FullBand p q)
    (hR : ((lduProductDerivative (factorBase a d b)).comp B).comp R=
      ContinuousLinearMap.id ℝ (FullBand p q)) :
    JointInverseRowsBounded a b := by
  have ha : ∀ i<p,∀ n,0<n → |reversedEntries a i n|≤M :=
    fun i hi n _ => reversedEntries_upper a haM i hi n
  have hb : ∀ i<q,∀ n,0<n → |reversedEntries b i n|≤M :=
    fun i hi n _ => reversedEntries_upper b hbM i hi n
  have hA := actualBase_derivative (reversedEntries a) (reversedEntries b) p q d hd M hM ha hb
  rw [reversed_factor_base] at hA
  let F := B (R (identityBand p q))
  refine ⟨‖F‖,actual_row_bound_of_identity_solution (reversedEntries a) (reversedEntries b)
    p q d hd (lduProductDerivative (factorBase a d b)) hA F ?_⟩
  exact congrArg (fun C : FullBand p q →L[ℝ] FullBand p q => C (identityBand p q)) hR

/-- Equivalence of differentiable and analytic positive full-band
factor choices. Differentiability is required only at the base matrix. -/
theorem full_free_differentiable_iff_analytic (p q : ℕ)
    (a : Fin (p+1) → Seq) (d : Seq) (b : Fin (q+1) → Seq)
    {α M : ℝ} (hα : 0<α) (hM : 0≤M)
    (ha : ∀ i n,α≤a i n) (hb : ∀ j n,α≤b j n) (hd : ∀ n,α≤d n)
    (haM : ∀ i n,|a i n|≤M) (hbM : ∀ j n,|b j n|≤M) :
    FullFreePositiveDifferentiableChoice a d b ↔ FullFreePositiveAnalyticChoice a d b := by
  constructor
  · intro hchoice
    obtain ⟨R,hR⟩ := full_free_differentiable_rightInverse a d b hchoice
    have hdne : ∀ n,d n≠0 := fun n => ne_of_gt (lt_of_lt_of_le hα (hd n))
    have hinj := factorBase_derivative_injective a d b hdne hM haM hbM
    obtain ⟨hL,hU⟩ := block_derivative_right_inverses
      (lduProductDerivative (factorBase a d b)) (freeTriangularDerivative a b) R
      (freeProductDerivative (p+1) a) (freeProductDerivative (q+1) b)
      (fun _ => rfl) hinj hR
    have hpa := (freeProductDerivative_rightInverse_iff_pairs (p+1) a α hα ha).mp hL
    have hpb := (freeProductDerivative_rightInverse_iff_pairs (q+1) b α hα hb).mp hU
    have hrows := joint_rows_of_composed_rightInverse a d b hdne hM haM hbM
      (freeTriangularDerivative a b) R hR
    exact (full_free_positive_factorization_iff p q a d b hα hM ha hb hd haM hbM).mpr
      ⟨hpa,hpb,hrows⟩
  · rintro ⟨g,hg,hg0,hprod⟩
    exact ⟨g,hg.differentiableAt,hg0,hprod⟩

theorem full_free_differentiable_factorization_iff_manuscript (p q : ℕ)
    (a : Fin (p+1) → Seq) (d : Seq) (b : Fin (q+1) → Seq)
    {α M : ℝ} (hα : 0<α) (hM : 0≤M)
    (ha : ∀ i n,α≤a i n) (hb : ∀ j n,α≤b j n) (hd : ∀ n,α≤d n)
    (haM : ∀ i n,|a i n|≤M) (hbM : ∀ j n,|b j n|≤M) :
    FullFreePositiveDifferentiableChoice a d b ↔
      ManuscriptFreePairCondition (p+1) a ∧ ManuscriptFreePairCondition (q+1) b ∧
      JointInverseRowsBounded a b := by
  rw [full_free_differentiable_iff_analytic p q a d b hα hM ha hb hd haM hbM,
    full_free_positive_factorization_iff_manuscript p q a d b hα hM ha hb hd haM hbM]

#print axioms full_free_differentiable_iff_analytic
#print axioms full_free_differentiable_factorization_iff_manuscript
end BTP.GeneralStability
