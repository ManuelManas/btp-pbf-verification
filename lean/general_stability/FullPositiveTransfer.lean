import AnalyticLDUCriterion
import AnalyticLowerStability

/-! Composition of actual triangular factor choices with normalized LDU.
The statements use the actual multiplication maps, not abstract stand-ins.
Uniform positivity follows from continuity in the Banach sequence norm. -/

noncomputable section
open Filter
open scoped Topology
namespace BTP.GeneralStability

/-- The normalized triangular data determined by two bidiagonal factor lists. -/
def factorBase {p q : ℕ} (a : Fin p → Seq) (d : Seq) (b : Fin q → Seq) :
    FullBand p q := (lowerProductBand a,d,lowerProductBand b)

/-- Complete multiplication, with the prescribed initial factor entries held fixed. -/
def fixedFullProduct {p q : ℕ} (a : Fin p → Seq) (d : Seq) (b : Fin q → Seq)
    (h : FullBand p q) : FullBand p q :=
  lduProduct (fixedProduct a h.1,d+h.2.1,fixedProduct b h.2.2)

@[simp] theorem fixedFullProduct_zero {p q : ℕ}
    (a : Fin p → Seq) (d : Seq) (b : Fin q → Seq) :
    fixedFullProduct a d b 0=lduProduct (factorBase a d b) := by
  simp [fixedFullProduct,factorBase]

/-- Positive analytic factorization of every nearby matrix, with all the
initial entries in each triangular side held fixed. -/
def FullFixedPositiveAnalyticChoice {p q : ℕ}
    (a : Fin p → Seq) (d : Seq) (b : Fin q → Seq) : Prop :=
  ∃ g : FullBand p q → FullBand p q,
    AnalyticAt ℝ g (lduProduct (factorBase a d b)) ∧
    g (lduProduct (factorBase a d b))=0 ∧
    (∀ᶠ T in 𝓝 (lduProduct (factorBase a d b)),
      fixedFullProduct a d b (g T)=T ∧
      (∀ i n, 1≤n → 0<perturbedFactors a (g T).1 i n) ∧
      (∀ j n, 1≤n → 0<perturbedFactors b (g T).2.2 j n) ∧
      (∀ n, 0<(d+(g T).2.1) n) ∧
      (∀ i n, n<p-i.val → perturbedFactors a (g T).1 i n=a i n) ∧
      (∀ j n, n<q-j.val → perturbedFactors b (g T).2.2 j n=b j n))

/-- Transfer from normalized LDU and the two triangular factor choices.
There are no additional regularity assumptions on multiplication. -/
theorem full_fixed_positive_of_ldu_and_triangular {p q : ℕ}
    (a : Fin p → Seq) (d : Seq) (b : Fin q → Seq)
    {α : ℝ} (hα : 0<α) (hd : ∀ n, α≤d n)
    (hL : FixedPositiveAnalyticChoice a) (hU : FixedPositiveAnalyticChoice b)
    (hldu : BTP.Stability.BandLDU.AnalyticLDUSection (factorBase a d b)) :
    FullFixedPositiveAnalyticChoice a d b := by
  obtain ⟨gL,hgL,hgL0,hgLP⟩ := hL
  obtain ⟨gU,hgU,hgU0,hgUP⟩ := hU
  obtain ⟨f,hf,hf0,hfP⟩ := hldu
  let T0 := lduProduct (factorBase a d b)
  have hfL : AnalyticAt ℝ (fun T => (f T).1) T0 :=
    ((lowerProjection p q).analyticAt _).comp hf
  have hfD : AnalyticAt ℝ (fun T => (f T).2.1) T0 :=
    ((diagonalProjection p q).analyticAt _).comp hf
  have hfU : AnalyticAt ℝ (fun T => (f T).2.2) T0 :=
    ((upperProjection p q).analyticAt _).comp hf
  have hfL0 : (f T0).1=lowerProductBand a := congrArg Prod.fst hf0
  have hfD0 : (f T0).2.1=d := congrArg (fun x : FullBand p q => x.2.1) hf0
  have hfU0 : (f T0).2.2=lowerProductBand b :=
    congrArg (fun x : FullBand p q => x.2.2) hf0
  have haL : AnalyticAt ℝ (fun T => gL ((f T).1)) T0 := by
    apply AnalyticAt.comp _ hfL
    simpa only [hfL0] using hgL
  have haU : AnalyticAt ℝ (fun T => gU ((f T).2.2)) T0 := by
    apply AnalyticAt.comp _ hfU
    simpa only [hfU0] using hgU
  let g : FullBand p q → FullBand p q :=
    fun T => (gL ((f T).1),(f T).2.1-d,gU ((f T).2.2))
  have hg : AnalyticAt ℝ g T0 := haL.prod ((hfD.sub analyticAt_const).prod haU)
  have hg0 : g T0=0 := by
    simp only [g,hfL0,hfD0,hfU0,hgL0,hgU0,sub_self]
    rfl
  have hLp : ∀ᶠ T in 𝓝 T0,
      fixedProduct a (gL ((f T).1))=(f T).1 ∧
      (∀ i n, 1≤n → 0<perturbedFactors a (gL ((f T).1)) i n) ∧
      (∀ i n, n<p-i.val → perturbedFactors a (gL ((f T).1)) i n=a i n) :=
    (show Tendsto (fun T => (f T).1) (𝓝 T0) (𝓝 (lowerProductBand a)) by
      simpa only [ContinuousAt,hfL0] using hfL.continuousAt).eventually hgLP
  have hUp : ∀ᶠ T in 𝓝 T0,
      fixedProduct b (gU ((f T).2.2))=(f T).2.2 ∧
      (∀ j n, 1≤n → 0<perturbedFactors b (gU ((f T).2.2)) j n) ∧
      (∀ j n, n<q-j.val → perturbedFactors b (gU ((f T).2.2)) j n=b j n) :=
    (show Tendsto (fun T => (f T).2.2) (𝓝 T0) (𝓝 (lowerProductBand b)) by
      simpa only [ContinuousAt,hfU0] using hfU.continuousAt).eventually hgUP
  have hDsmall : ∀ᶠ T in 𝓝 T0, ‖(f T).2.1-d‖<α := by
    have ht : Tendsto (fun T => (f T).2.1-d) (𝓝 T0) (𝓝 0) := by
      have hc : ContinuousAt (fun T : FullBand p q => (f T).2.1-d) T0 :=
        hfD.continuousAt.sub continuousAt_const
      change Tendsto (fun T : FullBand p q => (f T).2.1-d) (𝓝 T0) (𝓝 ((f T0).2.1-d)) at hc
      simpa only [hfD0,sub_self] using hc
    simpa only [Metric.mem_ball,dist_zero_right] using
      ht.eventually (Metric.ball_mem_nhds (0 : Seq) hα)
  refine ⟨g,hg,hg0,?_⟩
  filter_upwards [hfP,hLp,hUp,hDsmall] with T hprod hleft hright hsmall
  refine ⟨?_,hleft.2.1,hright.2.1,?_,hleft.2.2,hright.2.2⟩
  · simp only [fixedFullProduct,g,hleft.1,hright.1,add_sub_cancel]
    exact hprod
  · intro n
    have he := BTP.Stability.boundedSequence_abs_le ((f T).2.1-d) n
    have hb := (abs_le.mp he).1
    have hd0 := hd n
    change 0<(d+((f T).2.1-d)) n
    simp only [add_sub_cancel]
    change -(‖(f T).2.1-d‖)≤(f T).2.1 n-d n at hb
    linarith

/-- Uniform geometric criteria on each triangular side may be substituted
directly into the transfer theorem. -/
theorem full_fixed_positive_of_ldu_and_adjacent {p q : ℕ}
    (a : Fin p → Seq) (d : Seq) (b : Fin q → Seq)
    {α : ℝ} (hα : 0<α) (ha : ∀ i n, α≤a i n)
    (hd : ∀ n, α≤d n) (hb : ∀ j n, α≤b j n)
    (hga : ManuscriptAdjacentGeometric p a) (hgb : ManuscriptAdjacentGeometric q b)
    (hldu : BTP.Stability.BandLDU.AnalyticLDUSection (factorBase a d b)) :
    FullFixedPositiveAnalyticChoice a d b := by
  exact full_fixed_positive_of_ldu_and_triangular a d b hα hd
    ((fixed_initial_positive_factorization_iff_manuscript p a α hα ha).mpr hga)
    ((fixed_initial_positive_factorization_iff_manuscript q b α hα hb).mpr hgb) hldu

#print axioms full_fixed_positive_of_ldu_and_triangular
#print axioms full_fixed_positive_of_ldu_and_adjacent
end BTP.GeneralStability
