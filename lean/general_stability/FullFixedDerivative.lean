import FullPositiveTransfer
import AnalyticProductDerivative

noncomputable section
open Filter
open scoped Topology
namespace BTP.GeneralStability

def fixedTriangularMap {p q : ℕ} (a : Fin p → Seq) (d : Seq) (b : Fin q → Seq)
    (h : FullBand p q) : FullBand p q :=
  (fixedProduct a h.1,d+h.2.1,fixedProduct b h.2.2)

@[simp] theorem fixedTriangularMap_zero {p q : ℕ}
    (a : Fin p → Seq) (d : Seq) (b : Fin q → Seq) :
    fixedTriangularMap a d b 0 = factorBase a d b := by
  simp [fixedTriangularMap,factorBase]

def fixedTriangularDerivative {p q : ℕ} (a : Fin p → Seq) (b : Fin q → Seq) :
    FullBand p q →L[ℝ] FullBand p q :=
  ((fixedProductDerivative p a).comp (lowerProjection p q)).prod
    ((diagonalProjection p q).prod
      ((fixedProductDerivative q b).comp (upperProjection p q)))

@[simp] theorem fixedTriangularDerivative_apply {p q : ℕ}
    (a : Fin p → Seq) (b : Fin q → Seq) (h : FullBand p q) :
    fixedTriangularDerivative a b h =
      (fixedProductDerivative p a h.1,h.2.1,fixedProductDerivative q b h.2.2) := rfl

theorem analytic_fixedTriangularMap {p q : ℕ}
    (a : Fin p → Seq) (d : Seq) (b : Fin q → Seq) (h : FullBand p q) :
    AnalyticAt ℝ (fixedTriangularMap a d b) h := by
  have hL := (analytic_fixedProduct p a h.1).comp
    (f := fun v : FullBand p q => v.1) ((lowerProjection p q).analyticAt h)
  have hD : AnalyticAt ℝ (fun v : FullBand p q => d+v.2.1) h :=
    analyticAt_const.add ((diagonalProjection p q).analyticAt h)
  have hU := (analytic_fixedProduct q b h.2.2).comp
    (f := fun v : FullBand p q => v.2.2) ((upperProjection p q).analyticAt h)
  exact hL.prod (hD.prod hU)

theorem fixedTriangularMap_hasFDerivAt {p q : ℕ}
    (a : Fin p → Seq) (d : Seq) (b : Fin q → Seq) :
    HasFDerivAt (fixedTriangularMap a d b) (fixedTriangularDerivative a b) 0 := by
  have hL := (fixedProduct_hasFDerivAt p a).comp (0 : FullBand p q)
    (lowerProjection p q).hasFDerivAt
  have hD := (hasFDerivAt_const d (0 : FullBand p q)).add
    (diagonalProjection p q).hasFDerivAt
  have hU := (fixedProduct_hasFDerivAt q b).comp (0 : FullBand p q)
    (upperProjection p q).hasFDerivAt
  simp only [zero_add] at hD
  convert hL.prodMk (hD.prodMk hU) using 1 <;> rfl

theorem analytic_fixedFullProduct {p q : ℕ}
    (a : Fin p → Seq) (d : Seq) (b : Fin q → Seq) (h : FullBand p q) :
    AnalyticAt ℝ (fixedFullProduct a d b) h := by
  exact (analytic_lduProduct _).comp (analytic_fixedTriangularMap a d b h)

theorem fixedFullProduct_hasFDerivAt {p q : ℕ}
    (a : Fin p → Seq) (d : Seq) (b : Fin q → Seq) :
    HasFDerivAt (fixedFullProduct a d b)
      ((lduProductDerivative (factorBase a d b)).comp (fixedTriangularDerivative a b)) 0 := by
  have hldu : HasFDerivAt (@lduProduct p q) (lduProductDerivative (factorBase a d b))
      (fixedTriangularMap a d b 0) := by
    rw [fixedTriangularMap_zero]
    exact lduProduct_hasFDerivAt _
  convert hldu.comp 0 (fixedTriangularMap_hasFDerivAt a d b) using 1 <;> rfl

/-- Any analytic positive full factor choice yields an analytic choice
of its normalized LDU, by multiplying within each triangular side. -/
theorem full_fixed_choice_implies_analytic_ldu {p q : ℕ}
    (a : Fin p → Seq) (d : Seq) (b : Fin q → Seq)
    (hchoice : FullFixedPositiveAnalyticChoice a d b) :
    BTP.Stability.BandLDU.AnalyticLDUSection (factorBase a d b) := by
  obtain ⟨g,hg,hg0,hprod⟩ := hchoice
  refine ⟨fun T => fixedTriangularMap a d b (g T), ?_, ?_, ?_⟩
  · convert (analytic_fixedTriangularMap a d b (g (lduProduct (factorBase a d b)))).comp
      (f := g) hg using 1
    rfl
  · change fixedTriangularMap a d b (g (lduProduct (factorBase a d b))) = _
    rw [hg0,fixedTriangularMap_zero]
  · exact hprod.mono (fun _ h => h.1)

/-- The differentiated local section is a genuine bounded right inverse
of the composed full-band multiplication derivative. -/
theorem full_fixed_choice_derivative_rightInverse {p q : ℕ}
    (a : Fin p → Seq) (d : Seq) (b : Fin q → Seq)
    (hchoice : FullFixedPositiveAnalyticChoice a d b) :
    ∃ R : FullBand p q →L[ℝ] FullBand p q,
      (((lduProductDerivative (factorBase a d b)).comp
        (fixedTriangularDerivative a b)).comp R) = ContinuousLinearMap.id ℝ (FullBand p q) := by
  obtain ⟨g,hg,hg0,hprod⟩ := hchoice
  have hga : g (fixedFullProduct a d b 0) = 0 := by
    simpa only [fixedFullProduct_zero] using hg0
  have hgd : HasFDerivAt g (fderiv ℝ g (fixedFullProduct a d b 0))
      (fixedFullProduct a d b 0) := by
    simpa only [fixedFullProduct_zero] using hg.differentiableAt.hasFDerivAt
  have hright : ∀ᶠ T in 𝓝 (fixedFullProduct a d b 0), fixedFullProduct a d b (g T) = T := by
    simpa only [fixedFullProduct_zero] using hprod.mono (fun _ h => h.1)
  exact ⟨_,BTP.AnalyticFactorization.derivative_right_inverse_of_section
    (fixedFullProduct_hasFDerivAt a d b) hgd hga hright⟩

#print axioms fixedFullProduct_hasFDerivAt
#print axioms full_fixed_choice_implies_analytic_ldu
#print axioms full_fixed_choice_derivative_rightInverse

end BTP.GeneralStability
