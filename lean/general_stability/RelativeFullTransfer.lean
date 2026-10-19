import RelativeLowerCriterion
import RelativeLDUMatrix

noncomputable section
open Filter
open scoped Topology
namespace BTP.RelativeStability
open BTP.GeneralStability

def relativeFactorBase {p : ℕ} (a : Fin p → ℕ → ℝ) (r : Fin p) (j : ℕ) : ℝ :=
  rawCoefficient (extendRaw a) p (r.val+1) j

theorem relativeFactorBase_pos {p : ℕ} (a : Fin p → ℕ → ℝ)
    (ha : ∀ i n,0<a i n) : ∀ r j,0<relativeFactorBase a r j := by
  intro r j
  exact rawCoefficient_pos (extendRaw a) (extendRaw_pos a ha) p (r.val+1) j (by omega)

def relativeTriangularMap {p q : ℕ} (a : Fin p → ℕ → ℝ) (b : Fin q → ℕ → ℝ)
    (ha : ∀ i n,0<a i n) (hb : ∀ i n,0<b i n) (h : FullBand p q) : FullBand p q :=
  (relativeProduct a ha h.1,h.2.1,relativeProduct b hb h.2.2)

def relativeTriangularDerivative {p q : ℕ} (a : Fin p → ℕ → ℝ) (b : Fin q → ℕ → ℝ)
    (ha : ∀ i n,0<a i n) (hb : ∀ i n,0<b i n) : FullBand p q →L[ℝ] FullBand p q :=
  ((relativeProductDerivative a ha 0).comp (lowerProjection p q)).prod
    ((diagonalProjection p q).prod ((relativeProductDerivative b hb 0).comp (upperProjection p q)))

@[simp] theorem relativeTriangularMap_zero {p q : ℕ}
    (a : Fin p → ℕ → ℝ) (b : Fin q → ℕ → ℝ)
    (ha : ∀ i n,0<a i n) (hb : ∀ i n,0<b i n) : relativeTriangularMap a b ha hb 0=0 := by
  simp [relativeTriangularMap]

theorem analytic_relativeTriangularMap {p q : ℕ}
    (a : Fin p → ℕ → ℝ) (b : Fin q → ℕ → ℝ)
    (ha : ∀ i n,0<a i n) (hb : ∀ i n,0<b i n) (h : FullBand p q) :
    AnalyticAt ℝ (relativeTriangularMap a b ha hb) h :=
  ((analytic_relativeProduct a ha h.1).comp (f:=fun v : FullBand p q=>v.1)
    ((lowerProjection p q).analyticAt h)).prod
    (((diagonalProjection p q).analyticAt h).prod
      ((analytic_relativeProduct b hb h.2.2).comp (f:=fun v : FullBand p q=>v.2.2)
        ((upperProjection p q).analyticAt h)))

theorem relativeTriangularMap_hasFDerivAt {p q : ℕ}
    (a : Fin p → ℕ → ℝ) (b : Fin q → ℕ → ℝ)
    (ha : ∀ i n,0<a i n) (hb : ∀ i n,0<b i n) :
    HasFDerivAt (relativeTriangularMap a b ha hb) (relativeTriangularDerivative a b ha hb) 0 := by
  have hL := (relativeProduct_hasFDerivAt a ha 0).comp (0 : FullBand p q) (lowerProjection p q).hasFDerivAt
  have hU := (relativeProduct_hasFDerivAt b hb 0).comp (0 : FullBand p q) (upperProjection p q).hasFDerivAt
  convert hL.prodMk ((diagonalProjection p q).hasFDerivAt.prodMk hU) using 1 <;> rfl

def relativeFullProduct {p q : ℕ} (a : Fin p → ℕ → ℝ) (d : ℕ → ℝ) (b : Fin q → ℕ → ℝ)
    (ha : ∀ i n,0<a i n) (hd : ∀ n,0<d n) (hb : ∀ i n,0<b i n) (h : FullBand p q) : FullBand p q :=
  relativeLDUProduct (relativeFactorBase a) d (relativeFactorBase b)
    (relativeFactorBase_pos a ha) hd (relativeFactorBase_pos b hb) (relativeTriangularMap a b ha hb h)

@[simp] theorem relativeFullProduct_zero {p q : ℕ}
    (a : Fin p → ℕ → ℝ) (d : ℕ → ℝ) (b : Fin q → ℕ → ℝ)
    (ha : ∀ i n,0<a i n) (hd : ∀ n,0<d n) (hb : ∀ i n,0<b i n) :
    relativeFullProduct a d b ha hd hb 0=0 := by
  simp [relativeFullProduct]

theorem analytic_relativeFullProduct {p q : ℕ}
    (a : Fin p → ℕ → ℝ) (d : ℕ → ℝ) (b : Fin q → ℕ → ℝ)
    (ha : ∀ i n,0<a i n) (hd : ∀ n,0<d n) (hb : ∀ i n,0<b i n) (h : FullBand p q) :
    AnalyticAt ℝ (relativeFullProduct a d b ha hd hb) h :=
  (analytic_relativeLDUProduct _ _ _ _ _ _ _).comp (analytic_relativeTriangularMap a b ha hb h)

theorem relativeFullProduct_hasFDerivAt {p q : ℕ}
    (a : Fin p → ℕ → ℝ) (d : ℕ → ℝ) (b : Fin q → ℕ → ℝ)
    (ha : ∀ i n,0<a i n) (hd : ∀ n,0<d n) (hb : ∀ i n,0<b i n) :
    HasFDerivAt (relativeFullProduct a d b ha hd hb)
      ((relativeLDUProductDerivative (relativeFactorBase a) d (relativeFactorBase b)
        (relativeFactorBase_pos a ha) hd (relativeFactorBase_pos b hb) 0).comp
        (relativeTriangularDerivative a b ha hb)) 0 := by
  have hl := relativeLDUProduct_hasFDerivAt (relativeFactorBase a) d (relativeFactorBase b)
    (relativeFactorBase_pos a ha) hd (relativeFactorBase_pos b hb) 0
  rw [←relativeTriangularMap_zero a b ha hb] at hl
  convert hl.comp 0 (relativeTriangularMap_hasFDerivAt a b ha hb) using 1 <;>
    first | rfl | simp only [relativeTriangularMap_zero]

def RelativeAnalyticLDUSection {p q : ℕ} (l : Fin p → ℕ → ℝ) (d : ℕ → ℝ) (u : Fin q → ℕ → ℝ)
    (hl : ∀ i n,0<l i n) (hd : ∀ n,0<d n) (hu : ∀ i n,0<u i n) : Prop :=
  ∃ f : FullBand p q → FullBand p q,AnalyticAt ℝ f 0 ∧ f 0=0 ∧
    ∀ᶠ E in 𝓝 (0 : FullBand p q),relativeLDUProduct l d u hl hd hu (f E)=E

def RelativeFullPositiveAnalyticChoice {p q : ℕ}
    (a : Fin p → ℕ → ℝ) (d : ℕ → ℝ) (b : Fin q → ℕ → ℝ)
    (ha : ∀ i n,0<a i n) (hd : ∀ n,0<d n) (hb : ∀ i n,0<b i n) : Prop :=
  ∃ g : FullBand p q → FullBand p q,AnalyticAt ℝ g 0 ∧ g 0=0 ∧
    (∀ᶠ E in 𝓝 (0 : FullBand p q),relativeFullProduct a d b ha hd hb (g E)=E ∧
      (∀ i n,1≤n → 0<relativePerturbedFactor a (g E).1 i n) ∧
      (∀ i n,1≤n → 0<relativePerturbedFactor b (g E).2.2 i n) ∧
      (∀ n,0<d n*(1+(g E).2.1 n)) ∧
      (∀ i n,n<p-i.val → relativePerturbedFactor a (g E).1 i n=a i n) ∧
      (∀ i n,n<q-i.val → relativePerturbedFactor b (g E).2.2 i n=b i n))

theorem relative_full_choice_implies_analytic_ldu {p q : ℕ}
    (a : Fin p → ℕ → ℝ) (d : ℕ → ℝ) (b : Fin q → ℕ → ℝ)
    (ha : ∀ i n,0<a i n) (hd : ∀ n,0<d n) (hb : ∀ i n,0<b i n)
    (hc : RelativeFullPositiveAnalyticChoice a d b ha hd hb) :
    RelativeAnalyticLDUSection (relativeFactorBase a) d (relativeFactorBase b)
      (relativeFactorBase_pos a ha) hd (relativeFactorBase_pos b hb) := by
  obtain ⟨g,hg,hg0,hprod⟩ := hc
  refine ⟨fun E=>relativeTriangularMap a b ha hb (g E),?_,?_,?_⟩
  · exact (analytic_relativeTriangularMap a b ha hb (g 0)).comp hg
  · change relativeTriangularMap a b ha hb (g 0)=0
    rw [hg0,relativeTriangularMap_zero]
  · exact hprod.mono (fun _ h=>h.1)

theorem relative_full_choice_derivative_rightInverse {p q : ℕ}
    (a : Fin p → ℕ → ℝ) (d : ℕ → ℝ) (b : Fin q → ℕ → ℝ)
    (ha : ∀ i n,0<a i n) (hd : ∀ n,0<d n) (hb : ∀ i n,0<b i n)
    (hc : RelativeFullPositiveAnalyticChoice a d b ha hd hb) :
    ∃ R : FullBand p q →L[ℝ] FullBand p q,
      (((relativeLDUProductDerivative (relativeFactorBase a) d (relativeFactorBase b)
        (relativeFactorBase_pos a ha) hd (relativeFactorBase_pos b hb) 0).comp
        (relativeTriangularDerivative a b ha hb)).comp R)=ContinuousLinearMap.id ℝ _ := by
  obtain ⟨g,hg,hg0,hprod⟩ := hc
  have hga : g (relativeFullProduct a d b ha hd hb 0)=0 := by simpa using hg0
  have hgd : HasFDerivAt g (fderiv ℝ g (relativeFullProduct a d b ha hd hb 0))
      (relativeFullProduct a d b ha hd hb 0) := by simpa using hg.differentiableAt.hasFDerivAt
  have hr : ∀ᶠ E in 𝓝 (relativeFullProduct a d b ha hd hb 0),relativeFullProduct a d b ha hd hb (g E)=E := by
    simpa using hprod.mono (fun _ h=>h.1)
  exact ⟨_,BTP.AnalyticFactorization.derivative_right_inverse_of_section
    (relativeFullProduct_hasFDerivAt a d b ha hd hb) hgd hga hr⟩

theorem relative_full_positive_of_ldu_and_triangular {p q : ℕ}
    (a : Fin p → ℕ → ℝ) (d : ℕ → ℝ) (b : Fin q → ℕ → ℝ)
    (ha : ∀ i n,0<a i n) (hd : ∀ n,0<d n) (hb : ∀ i n,0<b i n)
    (hL : RelativePositiveAnalyticChoice a ha) (hU : RelativePositiveAnalyticChoice b hb)
    (hldu : RelativeAnalyticLDUSection (relativeFactorBase a) d (relativeFactorBase b)
      (relativeFactorBase_pos a ha) hd (relativeFactorBase_pos b hb)) :
    RelativeFullPositiveAnalyticChoice a d b ha hd hb := by
  obtain ⟨gL,hgL,hgL0,hgLP⟩ := hL
  obtain ⟨gU,hgU,hgU0,hgUP⟩ := hU
  obtain ⟨f,hf,hf0,hfP⟩ := hldu
  have hfL : AnalyticAt ℝ (fun E=>(f E).1) 0 := ((lowerProjection p q).analyticAt _).comp hf
  have hfD : AnalyticAt ℝ (fun E=>(f E).2.1) 0 := ((diagonalProjection p q).analyticAt _).comp hf
  have hfU : AnalyticAt ℝ (fun E=>(f E).2.2) 0 := ((upperProjection p q).analyticAt _).comp hf
  have hfL0 : (f 0).1=0 := congrArg Prod.fst hf0
  have hfD0 : (f 0).2.1=0 := congrArg (fun x : FullBand p q=>x.2.1) hf0
  have hfU0 : (f 0).2.2=0 := congrArg (fun x : FullBand p q=>x.2.2) hf0
  have haL : AnalyticAt ℝ (fun E=>gL ((f E).1)) 0 := by
    apply AnalyticAt.comp _ hfL
    simpa only [hfL0] using hgL
  have haU : AnalyticAt ℝ (fun E=>gU ((f E).2.2)) 0 := by
    apply AnalyticAt.comp _ hfU
    simpa only [hfU0] using hgU
  let g : FullBand p q → FullBand p q := fun E=>(gL ((f E).1),(f E).2.1,gU ((f E).2.2))
  have hg : AnalyticAt ℝ g 0 := haL.prod (hfD.prod haU)
  have hg0 : g 0=0 := by
    simp only [g,hfL0,hfD0,hfU0,hgL0,hgU0]
    rfl
  have hLp : ∀ᶠ E in 𝓝 (0 : FullBand p q),
      relativeProduct a ha (gL ((f E).1))=(f E).1 ∧
      (∀ i n,1≤n → 0<relativePerturbedFactor a (gL ((f E).1)) i n) ∧
      (∀ i n,n<p-i.val → relativePerturbedFactor a (gL ((f E).1)) i n=a i n) :=
    (show Tendsto (fun E=>(f E).1) (𝓝 (0 : FullBand p q)) (𝓝 0) by
      simpa only [ContinuousAt,hfL0] using hfL.continuousAt).eventually hgLP
  have hUp : ∀ᶠ E in 𝓝 (0 : FullBand p q),
      relativeProduct b hb (gU ((f E).2.2))=(f E).2.2 ∧
      (∀ i n,1≤n → 0<relativePerturbedFactor b (gU ((f E).2.2)) i n) ∧
      (∀ i n,n<q-i.val → relativePerturbedFactor b (gU ((f E).2.2)) i n=b i n) :=
    (show Tendsto (fun E=>(f E).2.2) (𝓝 (0 : FullBand p q)) (𝓝 0) by
      simpa only [ContinuousAt,hfU0] using hfU.continuousAt).eventually hgUP
  have hsmall : ∀ᶠ E in 𝓝 (0 : FullBand p q),‖(f E).2.1‖<1 := by
    have ht : Tendsto (fun E=>(f E).2.1) (𝓝 (0 : FullBand p q)) (𝓝 0) := by
      simpa only [ContinuousAt,hfD0] using hfD.continuousAt
    simpa only [Metric.mem_ball,dist_zero_right] using
      ht.eventually (Metric.ball_mem_nhds (0 : Seq) zero_lt_one)
  refine ⟨g,hg,hg0,?_⟩
  filter_upwards [hfP,hLp,hUp,hsmall] with E hprod hleft hright hsmall
  refine ⟨?_,hleft.2.1,hright.2.1,?_,hleft.2.2,hright.2.2⟩
  · simpa only [relativeFullProduct,relativeTriangularMap,g,hleft.1,hright.1] using hprod
  · intro n
    have he := (abs_le.mp (BTP.Stability.boundedSequence_abs_le ((f E).2.1) n)).1
    exact mul_pos (hd n) (by change 0<1+(f E).2.1 n; linarith)

theorem relative_full_positive_of_ldu_and_adjacent {p q : ℕ}
    (a : Fin p → ℕ → ℝ) (d : ℕ → ℝ) (b : Fin q → ℕ → ℝ)
    (ha : ∀ i n,0<a i n) (hd : ∀ n,0<d n) (hb : ∀ i n,0<b i n)
    (hga : RelativeAdjacentGeometric a) (hgb : RelativeAdjacentGeometric b)
    (hldu : RelativeAnalyticLDUSection (relativeFactorBase a) d (relativeFactorBase b)
      (relativeFactorBase_pos a ha) hd (relativeFactorBase_pos b hb)) :
    RelativeFullPositiveAnalyticChoice a d b ha hd hb :=
  relative_full_positive_of_ldu_and_triangular a d b ha hd hb
    ((relative_positive_choice_iff_adjacent p a ha).mpr hga)
    ((relative_positive_choice_iff_adjacent q b hb).mpr hgb) hldu

theorem relative_full_choice_with_lipschitz {p q : ℕ}
    (a : Fin p → ℕ → ℝ) (d : ℕ → ℝ) (b : Fin q → ℕ → ℝ)
    (ha : ∀ i n,0<a i n) (hd : ∀ n,0<d n) (hb : ∀ i n,0<b i n)
    (hc : RelativeFullPositiveAnalyticChoice a d b ha hd hb) :
    ∃ g : FullBand p q → FullBand p q,AnalyticAt ℝ g 0 ∧ g 0=0 ∧
      (∀ᶠ E in 𝓝 (0 : FullBand p q),relativeFullProduct a d b ha hd hb (g E)=E ∧
        (∀ i n,1≤n → 0<relativePerturbedFactor a (g E).1 i n) ∧
        (∀ i n,1≤n → 0<relativePerturbedFactor b (g E).2.2 i n) ∧
        (∀ n,0<d n*(1+(g E).2.1 n)) ∧
        (∀ i n,n<p-i.val → relativePerturbedFactor a (g E).1 i n=a i n) ∧
        (∀ i n,n<q-i.val → relativePerturbedFactor b (g E).2.2 i n=b i n)) ∧
      ∃ K,∃ s ∈ 𝓝 (0 : FullBand p q),LipschitzOnWith K g s := by
  obtain ⟨g,hg,hg0,hprod⟩ := hc
  exact ⟨g,hg,hg0,hprod,hg.hasStrictFDerivAt.exists_lipschitzOnWith⟩

theorem relative_analytic_ldu_of_right_inverse {p q : ℕ}
    (l : Fin p → ℕ → ℝ) (d : ℕ → ℝ) (u : Fin q → ℕ → ℝ)
    (hl : ∀ i n,0<l i n) (hd : ∀ n,0<d n) (hu : ∀ i n,0<u i n)
    (R : FullBand p q →L[ℝ] FullBand p q)
    (hR : (relativeLDUProductDerivative l d u hl hd hu 0).comp R=ContinuousLinearMap.id ℝ _) :
    RelativeAnalyticLDUSection l d u hl hd hu := by
  obtain ⟨g,hg,hg0,hr⟩ := BTP.AnalyticFactorization.analytic_local_section
    (analytic_relativeLDUProduct l d u hl hd hu 0) _ R
    (relativeLDUProduct_hasFDerivAt l d u hl hd hu 0) hR
  simp only [relativeLDUProduct_zero] at hg hg0 hr
  exact ⟨g,hg,hg0,hr⟩

theorem relative_analytic_ldu_derivative_rightInverse {p q : ℕ}
    (l : Fin p → ℕ → ℝ) (d : ℕ → ℝ) (u : Fin q → ℕ → ℝ)
    (hl : ∀ i n,0<l i n) (hd : ∀ n,0<d n) (hu : ∀ i n,0<u i n)
    (hc : RelativeAnalyticLDUSection l d u hl hd hu) :
    ∃ R : FullBand p q →L[ℝ] FullBand p q,
      (relativeLDUProductDerivative l d u hl hd hu 0).comp R=ContinuousLinearMap.id ℝ _ := by
  obtain ⟨g,hg,hg0,hr⟩ := hc
  have hga : g (relativeLDUProduct l d u hl hd hu 0)=0 := by simpa using hg0
  have hgd : HasFDerivAt g (fderiv ℝ g (relativeLDUProduct l d u hl hd hu 0))
      (relativeLDUProduct l d u hl hd hu 0) := by simpa using hg.differentiableAt.hasFDerivAt
  have hright : ∀ᶠ E in 𝓝 (relativeLDUProduct l d u hl hd hu 0),relativeLDUProduct l d u hl hd hu (g E)=E := by
    simpa using hr
  exact ⟨_,BTP.AnalyticFactorization.derivative_right_inverse_of_section
    (relativeLDUProduct_hasFDerivAt l d u hl hd hu 0) hgd hga hright⟩

/-- This transfer of necessity uses only formal injectivity of normalized
LDU. Bounded invertibility of LDU is not an assumption. -/
theorem relative_full_choice_implies_adjacent_of_ldu_injective {p q : ℕ}
    (a : Fin p → ℕ → ℝ) (d : ℕ → ℝ) (b : Fin q → ℕ → ℝ)
    (ha : ∀ i n,0<a i n) (hd : ∀ n,0<d n) (hb : ∀ i n,0<b i n)
    (hI : Function.Injective (relativeLDUProductDerivative (relativeFactorBase a) d (relativeFactorBase b)
      (relativeFactorBase_pos a ha) hd (relativeFactorBase_pos b hb) 0))
    (hc : RelativeFullPositiveAnalyticChoice a d b ha hd hb) :
    RelativeAdjacentGeometric a ∧ RelativeAdjacentGeometric b := by
  obtain ⟨R,hR⟩ := relative_full_choice_derivative_rightInverse a d b ha hd hb hc
  let A := relativeLDUProductDerivative (relativeFactorBase a) d (relativeFactorBase b)
    (relativeFactorBase_pos a ha) hd (relativeFactorBase_pos b hb) 0
  have hsurj : Function.Surjective (relativeTriangularDerivative a b ha hb) := by
    intro E
    refine ⟨R (A E),hI ?_⟩
    exact congrArg (fun M : FullBand p q →L[ℝ] FullBand p q=>M (A E)) hR
  constructor
  · apply (relativeProductDerivative_surjective_iff_adjacent p a ha).mp
    intro E
    obtain ⟨h,hh⟩ := hsurj (E,0,0)
    exact ⟨h.1,congrArg Prod.fst hh⟩
  · apply (relativeProductDerivative_surjective_iff_adjacent q b hb).mp
    intro E
    obtain ⟨h,hh⟩ := hsurj (0,0,E)
    exact ⟨h.2.2,congrArg (fun v : FullBand p q=>v.2.2) hh⟩

#print axioms relativeFullProduct_hasFDerivAt
#print axioms relative_full_choice_derivative_rightInverse
#print axioms relative_full_positive_of_ldu_and_adjacent
#print axioms relative_full_choice_with_lipschitz
#print axioms relative_full_choice_implies_adjacent_of_ldu_injective

end BTP.RelativeStability
