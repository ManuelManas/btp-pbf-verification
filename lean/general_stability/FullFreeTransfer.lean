import FullPositiveTransfer
import AnalyticFreeLowerStability

noncomputable section
open Filter
open scoped Topology
namespace BTP.GeneralStability

def freeTriangularMap {p q : ℕ} (a : Fin p → Seq) (d : Seq) (b : Fin q → Seq)
    (h : FullBand p q) : FullBand p q :=
  (freeProduct a h.1,d+h.2.1,freeProduct b h.2.2)

@[simp] theorem freeTriangularMap_zero {p q : ℕ}
    (a : Fin p → Seq) (d : Seq) (b : Fin q → Seq) :
    freeTriangularMap a d b 0 = factorBase a d b := by
  simp [freeTriangularMap,factorBase]

def freeFullProduct {p q : ℕ} (a : Fin p → Seq) (d : Seq) (b : Fin q → Seq)
    (h : FullBand p q) : FullBand p q := lduProduct (freeTriangularMap a d b h)

@[simp] theorem freeFullProduct_zero {p q : ℕ}
    (a : Fin p → Seq) (d : Seq) (b : Fin q → Seq) :
    freeFullProduct a d b 0 = lduProduct (factorBase a d b) := by
  simp [freeFullProduct]

def freeTriangularDerivative {p q : ℕ} (a : Fin p → Seq) (b : Fin q → Seq) :
    FullBand p q →L[ℝ] FullBand p q :=
  ((freeProductDerivative p a).comp (lowerProjection p q)).prod
    ((diagonalProjection p q).prod
      ((freeProductDerivative q b).comp (upperProjection p q)))

@[simp] theorem freeTriangularDerivative_apply {p q : ℕ}
    (a : Fin p → Seq) (b : Fin q → Seq) (h : FullBand p q) :
    freeTriangularDerivative a b h =
      (freeProductDerivative p a h.1,h.2.1,freeProductDerivative q b h.2.2) := rfl

theorem analytic_freeTriangularMap {p q : ℕ}
    (a : Fin p → Seq) (d : Seq) (b : Fin q → Seq) (h : FullBand p q) :
    AnalyticAt ℝ (freeTriangularMap a d b) h := by
  have hL := (analytic_freeProduct p a h.1).comp
    (f := fun v : FullBand p q => v.1) ((lowerProjection p q).analyticAt h)
  have hD : AnalyticAt ℝ (fun v : FullBand p q => d+v.2.1) h :=
    analyticAt_const.add ((diagonalProjection p q).analyticAt h)
  have hU := (analytic_freeProduct q b h.2.2).comp
    (f := fun v : FullBand p q => v.2.2) ((upperProjection p q).analyticAt h)
  exact hL.prod (hD.prod hU)

theorem freeTriangularMap_hasFDerivAt {p q : ℕ}
    (a : Fin p → Seq) (d : Seq) (b : Fin q → Seq) :
    HasFDerivAt (freeTriangularMap a d b) (freeTriangularDerivative a b) 0 := by
  have hL := (freeProduct_hasFDerivAt p a).comp (0 : FullBand p q)
    (lowerProjection p q).hasFDerivAt
  have hD := (hasFDerivAt_const d (0 : FullBand p q)).add
    (diagonalProjection p q).hasFDerivAt
  have hU := (freeProduct_hasFDerivAt q b).comp (0 : FullBand p q)
    (upperProjection p q).hasFDerivAt
  simp only [zero_add] at hD
  convert hL.prodMk (hD.prodMk hU) using 1 <;> rfl

theorem analytic_freeFullProduct {p q : ℕ}
    (a : Fin p → Seq) (d : Seq) (b : Fin q → Seq) (h : FullBand p q) :
    AnalyticAt ℝ (freeFullProduct a d b) h := by
  exact (analytic_lduProduct _).comp (analytic_freeTriangularMap a d b h)

theorem freeFullProduct_hasFDerivAt {p q : ℕ}
    (a : Fin p → Seq) (d : Seq) (b : Fin q → Seq) :
    HasFDerivAt (freeFullProduct a d b)
      ((lduProductDerivative (factorBase a d b)).comp (freeTriangularDerivative a b)) 0 := by
  have hldu : HasFDerivAt (@lduProduct p q) (lduProductDerivative (factorBase a d b))
      (freeTriangularMap a d b 0) := by
    rw [freeTriangularMap_zero]
    exact lduProduct_hasFDerivAt _
  convert hldu.comp 0 (freeTriangularMap_hasFDerivAt a d b) using 1 <;> rfl

def FullFreePositiveAnalyticChoice {p q : ℕ}
    (a : Fin p → Seq) (d : Seq) (b : Fin q → Seq) : Prop :=
  ∃ g : FullBand p q → FullBand p q,
    AnalyticAt ℝ g (lduProduct (factorBase a d b)) ∧
    g (lduProduct (factorBase a d b))=0 ∧
    (∀ᶠ T in 𝓝 (lduProduct (factorBase a d b)),
      freeFullProduct a d b (g T)=T ∧
      (∀ i n, 1≤n → 0<freePerturbedFactors a (g T).1 i n) ∧
      (∀ j n, 1≤n → 0<freePerturbedFactors b (g T).2.2 j n) ∧
      (∀ n, 0<(d+(g T).2.1) n))

theorem full_free_choice_implies_analytic_ldu {p q : ℕ}
    (a : Fin p → Seq) (d : Seq) (b : Fin q → Seq)
    (hchoice : FullFreePositiveAnalyticChoice a d b) :
    BTP.Stability.BandLDU.AnalyticLDUSection (factorBase a d b) := by
  obtain ⟨g,hg,hg0,hprod⟩ := hchoice
  refine ⟨fun T => freeTriangularMap a d b (g T), ?_, ?_, ?_⟩
  · convert (analytic_freeTriangularMap a d b (g (lduProduct (factorBase a d b)))).comp
      (f := g) hg using 1
    rfl
  · change freeTriangularMap a d b (g (lduProduct (factorBase a d b))) = _
    rw [hg0,freeTriangularMap_zero]
  · exact hprod.mono (fun _ h => h.1)

theorem full_free_choice_derivative_rightInverse {p q : ℕ}
    (a : Fin p → Seq) (d : Seq) (b : Fin q → Seq)
    (hchoice : FullFreePositiveAnalyticChoice a d b) :
    ∃ R : FullBand p q →L[ℝ] FullBand p q,
      (((lduProductDerivative (factorBase a d b)).comp
        (freeTriangularDerivative a b)).comp R) = ContinuousLinearMap.id ℝ (FullBand p q) := by
  obtain ⟨g,hg,hg0,hprod⟩ := hchoice
  have hga : g (freeFullProduct a d b 0) = 0 := by
    simpa only [freeFullProduct_zero] using hg0
  have hgd : HasFDerivAt g (fderiv ℝ g (freeFullProduct a d b 0))
      (freeFullProduct a d b 0) := by
    simpa only [freeFullProduct_zero] using hg.differentiableAt.hasFDerivAt
  have hright : ∀ᶠ T in 𝓝 (freeFullProduct a d b 0), freeFullProduct a d b (g T) = T := by
    simpa only [freeFullProduct_zero] using hprod.mono (fun _ h => h.1)
  exact ⟨_,BTP.AnalyticFactorization.derivative_right_inverse_of_section
    (freeFullProduct_hasFDerivAt a d b) hgd hga hright⟩

theorem full_free_positive_of_ldu_and_triangular {p q : ℕ}
    (a : Fin p → Seq) (d : Seq) (b : Fin q → Seq)
    {α : ℝ} (hα : 0<α) (hd : ∀ n, α≤d n)
    (hL : FreePositiveAnalyticChoice a) (hU : FreePositiveAnalyticChoice b)
    (hldu : BTP.Stability.BandLDU.AnalyticLDUSection (factorBase a d b)) :
    FullFreePositiveAnalyticChoice a d b := by
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
      freeProduct a (gL ((f T).1))=(f T).1 ∧
      (∀ i n, 1≤n → 0<freePerturbedFactors a (gL ((f T).1)) i n) :=
    (show Tendsto (fun T => (f T).1) (𝓝 T0) (𝓝 (lowerProductBand a)) by
      simpa only [ContinuousAt,hfL0] using hfL.continuousAt).eventually hgLP
  have hUp : ∀ᶠ T in 𝓝 T0,
      freeProduct b (gU ((f T).2.2))=(f T).2.2 ∧
      (∀ j n, 1≤n → 0<freePerturbedFactors b (gU ((f T).2.2)) j n) :=
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
  refine ⟨?_,hleft.2,hright.2,?_⟩
  · simp only [freeFullProduct,freeTriangularMap,g,hleft.1,hright.1,add_sub_cancel]
    exact hprod
  · intro n
    have he := BTP.Stability.boundedSequence_abs_le ((f T).2.1-d) n
    have hb := (abs_le.mp he).1
    have hd0 := hd n
    change 0<(d+((f T).2.1-d)) n
    simp only [add_sub_cancel]
    change -(‖(f T).2.1-d‖)≤(f T).2.1 n-d n at hb
    linarith

theorem full_free_positive_of_ldu_and_pairs {p q : ℕ}
    (a : Fin p → Seq) (d : Seq) (b : Fin q → Seq)
    {α : ℝ} (hα : 0<α) (ha : ∀ i n, α≤a i n)
    (hd : ∀ n, α≤d n) (hb : ∀ j n, α≤b j n)
    (hga : FreePairCondition p a) (hgb : FreePairCondition q b)
    (hldu : BTP.Stability.BandLDU.AnalyticLDUSection (factorBase a d b)) :
    FullFreePositiveAnalyticChoice a d b := by
  exact full_free_positive_of_ldu_and_triangular a d b hα hd
    ((free_initial_positive_factorization_iff_pairs p a α hα ha).mpr hga)
    ((free_initial_positive_factorization_iff_pairs q b α hα hb).mpr hgb) hldu

#print axioms freeFullProduct_hasFDerivAt
#print axioms full_free_choice_derivative_rightInverse
#print axioms full_free_positive_of_ldu_and_pairs

end BTP.GeneralStability
