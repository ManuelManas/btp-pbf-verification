import AnalyticExtraction
import AnalyticMatrixRealization

noncomputable section
namespace BTP.GeneralStability

theorem bandCoefficient_lowerProductBand {p : ℕ} (a : Fin p → Seq) (d : ℕ) :
    bandCoefficient (lowerProductBand a) d = productCoefficient (List.ofFn a) d := by
  cases d with
  | zero => simp
  | succ d =>
    by_cases hd : d < p
    · have hh := bandCoefficient_coordinate (lowerProductBand a) ⟨d,hd⟩
      exact hh
    · rw [bandCoefficient_outside _ _ (by omega)]
      symm
      apply productCoefficient_outside
      simpa using (show p < d+1 by omega)

/-- Exact recursive decomposition of the Banach-space multiplication map. -/
theorem lowerProductBand_cons {p : ℕ} (a : Seq) (b : Fin p → Seq) :
    lowerProductBand (Fin.cons a b) = leftExtraction p (a, lowerProductBand b) := by
  funext r
  simp only [lowerProductBand, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ,
    leftExtraction, bandCoefficient_lowerProductBand, productCoefficient]

def tailCLM (p : ℕ) : (Fin (p+1) → Seq) →L[ℝ] (Fin p → Seq) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj i.succ

@[simp] theorem tailCLM_apply (p : ℕ) (h : Fin (p+1) → Seq) :
    tailCLM p h = Fin.tail h := rfl

/-- The first variation starts at row p+1; the remaining p factors retain
exactly the initial-entry conventions of the smaller problem. -/
theorem fixedProduct_succ {p : ℕ} (a h : Fin (p+1) → Seq) :
    fixedProduct a h = leftExtraction p
      (a 0 + zeroExtension (p+1) (h 0), fixedProduct (Fin.tail a) (Fin.tail h)) := by
  have he : (fun i : Fin (p+1) => a i + zeroExtension (p+1-i.val) (h i)) =
      Fin.cons (a 0 + zeroExtension (p+1) (h 0))
        (fun i : Fin p => a i.succ + zeroExtension (p-i.val) (h i.succ)) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp [Nat.add_sub_add_right]
  rw [fixedProduct, he, lowerProductBand_cons]
  rfl

/-- Explicit derivative of fixed-initial-entry multiplication, obtained
by composing the extraction derivative with the derivative for the
remaining factors. -/
def fixedProductDerivative : (p : ℕ) → (Fin p → Seq) →
    FactorVariations p →L[ℝ] LowerBand p
  | 0, _ => 0
  | p+1, a => (leftExtractionDerivative (a 0) (lowerProductBand (Fin.tail a))).comp
      (((zeroExtension (p+1)).comp (ContinuousLinearMap.proj 0)).prod
        ((fixedProductDerivative p (Fin.tail a)).comp (tailCLM p)))

theorem fixedProduct_hasFDerivAt (p : ℕ) (a : Fin p → Seq) :
    HasFDerivAt (fixedProduct a) (fixedProductDerivative p a) 0 := by
  induction p with
  | zero =>
    have he : fixedProduct a = fun _ => 0 := by
      funext h r
      exact Fin.elim0 r
    rw [he]
    exact hasFDerivAt_const _ _
  | succ p ih =>
    have hfirst : HasFDerivAt
        (fun h : Fin (p+1) → Seq => a 0 + zeroExtension (p+1) (h 0))
        ((zeroExtension (p+1)).comp (ContinuousLinearMap.proj 0)) 0 := by
      have hl := (zeroExtension (p+1)).hasFDerivAt.comp (0 : Fin (p+1) → Seq)
        (ContinuousLinearMap.proj (R := ℝ) (i := 0)).hasFDerivAt
      convert (hasFDerivAt_const (a 0) (0 : Fin (p+1) → Seq)).add hl using 1 <;>
        first | rfl | simp only [zero_add]
    have hsecond : HasFDerivAt
        (fun h : Fin (p+1) → Seq => fixedProduct (Fin.tail a) (Fin.tail h))
        ((fixedProductDerivative p (Fin.tail a)).comp (tailCLM p)) 0 := by
      have hh := (ih (Fin.tail a)).comp (0 : Fin (p+1) → Seq) (tailCLM p).hasFDerivAt
      convert hh using 1 <;> rfl
    have hinner := hfirst.prodMk hsecond
    have houter := leftExtraction_hasFDerivAt (a 0) (lowerProductBand (Fin.tail a))
    have hpoint : (a 0 + zeroExtension (p+1) ((0 : Fin (p+1) → Seq) 0),
        fixedProduct (Fin.tail a) (Fin.tail (0 : Fin (p+1) → Seq))) =
        (a 0, lowerProductBand (Fin.tail a)) := by
      change (a 0 + zeroExtension (p+1) 0, fixedProduct (Fin.tail a) 0) = _
      simp
    rw [←hpoint] at houter
    have hcomp := houter.comp (0 : Fin (p+1) → Seq) hinner
    convert hcomp using 1 <;> try rfl
    funext h
    exact fixedProduct_succ a h

#print axioms fixedProduct_succ
#print axioms fixedProduct_hasFDerivAt

end BTP.GeneralStability
