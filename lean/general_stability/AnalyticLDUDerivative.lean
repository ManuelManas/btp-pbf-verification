import AnalyticLDU

noncomputable section
set_option maxHeartbeats 800000
open scoped BigOperators
namespace BTP.GeneralStability

def lduTerm {p q : ℕ} (x : FullBand p q) (l u t : ℕ) : Seq :=
  zeroExtension t (bandCoefficient x.1 l * x.2.1 * bandCoefficient x.2.2 u)

def lduTermDerivative {p q : ℕ} (x : FullBand p q) (l u t : ℕ) :
    FullBand p q →L[ℝ] Seq :=
  (zeroExtension t).comp
    ((bandCoefficient x.1 l * x.2.1) •
        ((strictCoefficientMap q u).comp (upperProjection p q)) +
      bandCoefficient x.2.2 u •
        (bandCoefficient x.1 l • diagonalProjection p q +
          x.2.1 • ((strictCoefficientMap p l).comp (lowerProjection p q))))

theorem lduTerm_hasFDerivAt {p q : ℕ} (x : FullBand p q) (l u t : ℕ) :
    HasFDerivAt (fun y => lduTerm y l u t) (lduTermDerivative x l u t) x := by
  have hL : HasFDerivAt (fun y : FullBand p q => bandCoefficient y.1 l)
      ((strictCoefficientMap p l).comp (lowerProjection p q)) x := by
    convert (bandCoefficient_hasFDerivAt x.1 l).comp x (lowerProjection p q).hasFDerivAt
      using 1 <;> rfl
  have hD : HasFDerivAt (fun y : FullBand p q => y.2.1) (diagonalProjection p q) x :=
    (diagonalProjection p q).hasFDerivAt
  have hU : HasFDerivAt (fun y : FullBand p q => bandCoefficient y.2.2 u)
      ((strictCoefficientMap q u).comp (upperProjection p q)) x := by
    convert (bandCoefficient_hasFDerivAt x.2.2 u).comp x (upperProjection p q).hasFDerivAt
      using 1 <;> rfl
  have hprod := (hL.mul hD).mul hU
  convert (zeroExtension t).hasFDerivAt.comp x hprod using 1 <;> rfl

def lduLowerDerivative {p q : ℕ} (x : FullBand p q) (d : ℕ) : FullBand p q →L[ℝ] Seq :=
  ∑ t ∈ Finset.range (q+1), lduTermDerivative x (d+t) t t

def lduUpperDerivative {p q : ℕ} (x : FullBand p q) (d : ℕ) : FullBand p q →L[ℝ] Seq :=
  ∑ t ∈ Finset.range (p+1), lduTermDerivative x t (d+t) t

def lduProductDerivative {p q : ℕ} (x : FullBand p q) : FullBand p q →L[ℝ] FullBand p q :=
  (ContinuousLinearMap.pi fun r => lduLowerDerivative x (r.val+1)).prod
    ((lduLowerDerivative x 0).prod
      (ContinuousLinearMap.pi fun r => lduUpperDerivative x (r.val+1)))

theorem lduLowerCoefficient_hasFDerivAt {p q : ℕ} (x : FullBand p q) (d : ℕ) :
    HasFDerivAt (fun y => lduLowerCoefficient y d) (lduLowerDerivative x d) x := by
  have h := HasFDerivAt.fun_sum (u := Finset.range (q+1))
    (fun t _ => lduTerm_hasFDerivAt x (d+t) t t)
  convert h using 1 <;> rfl

theorem lduUpperCoefficient_hasFDerivAt {p q : ℕ} (x : FullBand p q) (d : ℕ) :
    HasFDerivAt (fun y => lduUpperCoefficient y d) (lduUpperDerivative x d) x := by
  have h := HasFDerivAt.fun_sum (u := Finset.range (p+1))
    (fun t _ => lduTerm_hasFDerivAt x t (d+t) t)
  convert h using 1 <;> rfl

/-- The Fréchet derivative of the actual LDU polynomial on the full fixed
band space. In matrix notation it is δL D U + L δD U + L D δU. -/
theorem lduProduct_hasFDerivAt {p q : ℕ} (x : FullBand p q) :
    HasFDerivAt (@lduProduct p q) (lduProductDerivative x) x := by
  have hl := hasFDerivAt_pi.mpr (fun r : Fin p => lduLowerCoefficient_hasFDerivAt x (r.val+1))
  have hd := lduLowerCoefficient_hasFDerivAt x 0
  have hu := hasFDerivAt_pi.mpr (fun r : Fin q => lduUpperCoefficient_hasFDerivAt x (r.val+1))
  convert hl.prodMk (hd.prodMk hu) using 1 <;> rfl

#print axioms lduTerm_hasFDerivAt
#print axioms lduProduct_hasFDerivAt

end BTP.GeneralStability
