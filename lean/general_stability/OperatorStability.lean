import BandOperatorNorm
import FullFixedEquivalence
import FullFreeCriterion

/-! Transport of the actual analytic factor choices to the space of banded
operators on real ℓ², endowed with its operator norm. -/
noncomputable section
open Filter
open scoped Topology
namespace BTP.GeneralStability

abbrev BandOperatorSpace (p q : ℕ) := (bandOperatorCLM p q).range

/-- All local predicates on the chosen factor variations, including exact
multiplication, positivity and fixed initial entries, are preserved by the
proved coefficient/operator continuous linear equivalence. -/
theorem analytic_choice_operator_iff {p q : ℕ} (T0 : FullBand p q)
    (P : FullBand p q → FullBand p q → Prop) :
    (∃ g : BandOperatorSpace p q → FullBand p q,
      AnalyticAt ℝ g (bandOperatorEquivRange p q T0) ∧
      g (bandOperatorEquivRange p q T0)=0 ∧
      ∀ᶠ A in 𝓝 (bandOperatorEquivRange p q T0),
        P ((bandOperatorEquivRange p q).symm A) (g A)) ↔
    (∃ g : FullBand p q → FullBand p q,
      AnalyticAt ℝ g T0 ∧ g T0=0 ∧ ∀ᶠ T in 𝓝 T0,P T (g T)) := by
  let e := bandOperatorEquivRange p q
  constructor
  · rintro ⟨g,hg,hg0,hP⟩
    refine ⟨fun T=>g (e T),?_,hg0,?_⟩
    · have hg' : AnalyticAt ℝ g (e T0) := hg
      have heA : AnalyticAt ℝ (fun T : FullBand p q=>e T) T0 :=
        ContinuousLinearEquiv.analyticAt (𝕜:=ℝ) (E:=FullBand p q)
          (F:=BandOperatorSpace p q) e T0
      exact hg'.comp heA
    · have he := e.continuous.continuousAt (x:=T0)
      have hp := he.tendsto.eventually hP
      simpa only [e,ContinuousLinearEquiv.symm_apply_apply] using hp
  · rintro ⟨g,hg,hg0,hP⟩
    refine ⟨fun A=>g (e.symm A),?_,?_,?_⟩
    · apply AnalyticAt.comp _ (e.symm.analyticAt (𝕜:=ℝ) (e T0))
      simpa only [ContinuousLinearEquiv.symm_apply_apply] using hg
    · change g (e.symm (e T0))=0
      simpa only [ContinuousLinearEquiv.symm_apply_apply] using hg0
    · have he : Tendsto e.symm (𝓝 (e T0)) (𝓝 T0) := by
        simpa only [ContinuousLinearEquiv.symm_apply_apply] using
          e.symm.continuous.continuousAt.tendsto (x:=e T0)
      exact he.eventually hP

/-- Positive factor choices, with fixed initial entries, on an actual
operator-norm neighborhood in the full band. -/
def FullFixedOperatorChoice {p q : ℕ}
    (a : Fin p → Seq) (d : Seq) (b : Fin q → Seq) : Prop :=
  ∃ g : BandOperatorSpace p q → FullBand p q,
    AnalyticAt ℝ g (bandOperatorEquivRange p q (lduProduct (factorBase a d b))) ∧
    g (bandOperatorEquivRange p q (lduProduct (factorBase a d b)))=0 ∧
    (∀ᶠ A in 𝓝 (bandOperatorEquivRange p q (lduProduct (factorBase a d b))),
      fixedFullProduct a d b (g A)=(bandOperatorEquivRange p q).symm A ∧
      (∀ i n,1≤n → 0<perturbedFactors a (g A).1 i n) ∧
      (∀ j n,1≤n → 0<perturbedFactors b (g A).2.2 j n) ∧
      (∀ n,0<(d+(g A).2.1) n) ∧
      (∀ i n,n<p-i.val → perturbedFactors a (g A).1 i n=a i n) ∧
      (∀ j n,n<q-j.val → perturbedFactors b (g A).2.2 j n=b j n))

theorem full_fixed_operator_choice_iff {p q : ℕ}
    (a : Fin p → Seq) (d : Seq) (b : Fin q → Seq) :
    FullFixedOperatorChoice a d b ↔ FullFixedPositiveAnalyticChoice a d b :=
by
  exact analytic_choice_operator_iff (lduProduct (factorBase a d b))
    (fun T h => fixedFullProduct a d b h=T ∧
      (∀ i n,1≤n → 0<perturbedFactors a h.1 i n) ∧
      (∀ j n,1≤n → 0<perturbedFactors b h.2.2 j n) ∧
      (∀ n,0<(d+h.2.1) n) ∧
      (∀ i n,n<p-i.val → perturbedFactors a h.1 i n=a i n) ∧
      (∀ j n,n<q-j.val → perturbedFactors b h.2.2 j n=b j n))

theorem full_fixed_operator_criterion (p q : ℕ)
    (a : Fin (p+1) → Seq) (d : Seq) (b : Fin (q+1) → Seq)
    {α M : ℝ} (hα : 0<α) (hM : 0≤M)
    (ha : ∀ i n,α≤a i n) (hb : ∀ j n,α≤b j n) (hd : ∀ n,α≤d n)
    (haM : ∀ i n,|a i n|≤M) (hbM : ∀ j n,|b j n|≤M) :
    FullFixedOperatorChoice a d b ↔
      ManuscriptAdjacentGeometric (p+1) a ∧ ManuscriptAdjacentGeometric (q+1) b ∧
      GeometricDecay (fun n=>a (Fin.last p) n*b (Fin.last q) n) := by
  rw [full_fixed_operator_choice_iff]
  exact full_fixed_positive_factorization_iff p q a d b hα hM ha hb hd haM hbM

/-- Positive factor choices with variable initial entries, measured in
operator norm on the prescribed full band. -/
def FullFreeOperatorChoice {p q : ℕ}
    (a : Fin p → Seq) (d : Seq) (b : Fin q → Seq) : Prop :=
  ∃ g : BandOperatorSpace p q → FullBand p q,
    AnalyticAt ℝ g (bandOperatorEquivRange p q (lduProduct (factorBase a d b))) ∧
    g (bandOperatorEquivRange p q (lduProduct (factorBase a d b)))=0 ∧
    (∀ᶠ A in 𝓝 (bandOperatorEquivRange p q (lduProduct (factorBase a d b))),
      freeFullProduct a d b (g A)=(bandOperatorEquivRange p q).symm A ∧
      (∀ i n,1≤n → 0<freePerturbedFactors a (g A).1 i n) ∧
      (∀ j n,1≤n → 0<freePerturbedFactors b (g A).2.2 j n) ∧
      (∀ n,0<(d+(g A).2.1) n))

theorem full_free_operator_choice_iff {p q : ℕ}
    (a : Fin p → Seq) (d : Seq) (b : Fin q → Seq) :
    FullFreeOperatorChoice a d b ↔ FullFreePositiveAnalyticChoice a d b := by
  exact analytic_choice_operator_iff (lduProduct (factorBase a d b))
    (fun T h => freeFullProduct a d b h=T ∧
      (∀ i n,1≤n → 0<freePerturbedFactors a h.1 i n) ∧
      (∀ j n,1≤n → 0<freePerturbedFactors b h.2.2 j n) ∧
      (∀ n,0<(d+h.2.1) n))

theorem full_free_operator_criterion (p q : ℕ)
    (a : Fin (p+1) → Seq) (d : Seq) (b : Fin (q+1) → Seq)
    {α M : ℝ} (hα : 0<α) (hM : 0≤M)
    (ha : ∀ i n,α≤a i n) (hb : ∀ j n,α≤b j n) (hd : ∀ n,α≤d n)
    (haM : ∀ i n,|a i n|≤M) (hbM : ∀ j n,|b j n|≤M) :
    FullFreeOperatorChoice a d b ↔
      ManuscriptFreePairCondition (p+1) a ∧ ManuscriptFreePairCondition (q+1) b ∧
      JointInverseRowsBounded a b := by
  rw [full_free_operator_choice_iff]
  exact full_free_positive_factorization_iff_manuscript p q a d b hα hM ha hb hd haM hbM

#print axioms full_free_operator_criterion
#print axioms analytic_choice_operator_iff
#print axioms full_fixed_operator_criterion
end BTP.GeneralStability
