import FreeExtraction
import AnalyticProductDerivative
import FreeForward

noncomputable section
namespace BTP.GeneralStability

/-- All actual factor entries may vary. The sequence coordinate zero is
the variation in row one; row zero of a unit bidiagonal is never varied. -/
def freeProduct {p : ℕ} (a h : Fin p → Seq) : LowerBand p :=
  lowerProductBand (fun i => a i + zeroExtension 1 (h i))

@[simp] theorem freeProduct_zero {p : ℕ} (a : Fin p → Seq) :
    freeProduct a 0 = lowerProductBand a := by
  simp only [freeProduct,Pi.zero_apply,map_zero,add_zero]

theorem freeProduct_succ {p : ℕ} (a h : Fin (p+1) → Seq) :
    freeProduct a h = leftExtraction p
      (a 0 + zeroExtension 1 (h 0), freeProduct (Fin.tail a) (Fin.tail h)) := by
  have he : (fun i : Fin (p+1) => a i + zeroExtension 1 (h i)) =
      Fin.cons (a 0 + zeroExtension 1 (h 0))
        (fun i : Fin p => a i.succ + zeroExtension 1 (h i.succ)) := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  rw [freeProduct,he,lowerProductBand_cons]
  rfl

theorem analytic_freeProduct (p : ℕ) (a x : Fin p → Seq) :
    AnalyticAt ℝ (freeProduct a) x := by
  have hi : AnalyticAt ℝ (fun h : Fin p → Seq => fun i => a i+zeroExtension 1 (h i)) x := by
    apply AnalyticAt.pi
    intro i
    exact analyticAt_const.add (((zeroExtension 1).analyticAt (x i)).comp
      (f := fun h : Fin p → Seq => h i) ((ContinuousLinearMap.proj (R := ℝ) i).analyticAt x))
  exact (analytic_lowerProductBand p _).comp hi

def freeProductDerivative : (p : ℕ) → (Fin p → Seq) →
    (Fin p → Seq) →L[ℝ] LowerBand p
  | 0, _ => 0
  | p+1, a => (freeExtractionDerivative (a 0) (lowerProductBand (Fin.tail a))).comp
      ((ContinuousLinearMap.proj 0).prod
        ((freeProductDerivative p (Fin.tail a)).comp (tailCLM p)))

theorem freeProduct_hasFDerivAt (p : ℕ) (a : Fin p → Seq) :
    HasFDerivAt (freeProduct a) (freeProductDerivative p a) 0 := by
  induction p with
  | zero =>
    have he : freeProduct a = fun _ => 0 := by
      funext h r
      exact Fin.elim0 r
    rw [he]
    exact hasFDerivAt_const _ _
  | succ p ih =>
    have hfirst : HasFDerivAt
        (fun h : Fin (p+1) → Seq => a 0 + zeroExtension 1 (h 0))
        ((zeroExtension 1).comp (ContinuousLinearMap.proj 0)) 0 := by
      have hl := (zeroExtension 1).hasFDerivAt.comp (0 : Fin (p+1) → Seq)
        (ContinuousLinearMap.proj (R := ℝ) (i := 0)).hasFDerivAt
      convert (hasFDerivAt_const (a 0) (0 : Fin (p+1) → Seq)).add hl using 1 <;>
        first | rfl | simp only [zero_add]
    have hsecond : HasFDerivAt
        (fun h : Fin (p+1) → Seq => freeProduct (Fin.tail a) (Fin.tail h))
        ((freeProductDerivative p (Fin.tail a)).comp (tailCLM p)) 0 := by
      have hh := (ih (Fin.tail a)).comp (0 : Fin (p+1) → Seq) (tailCLM p).hasFDerivAt
      convert hh using 1 <;> rfl
    have hinner := hfirst.prodMk hsecond
    have houter := leftExtraction_hasFDerivAt (a 0) (lowerProductBand (Fin.tail a))
    have hpoint : (a 0 + zeroExtension 1 ((0 : Fin (p+1) → Seq) 0),
        freeProduct (Fin.tail a) (Fin.tail (0 : Fin (p+1) → Seq))) =
        (a 0, lowerProductBand (Fin.tail a)) := by
      change (a 0 + zeroExtension 1 0,freeProduct (Fin.tail a) 0)=_
      simp
    rw [←hpoint] at houter
    have hcomp := houter.comp (0 : Fin (p+1) → Seq) hinner
    convert hcomp using 1 <;> try rfl
    · funext h
      exact freeProduct_succ a h

theorem freeProductDerivative_succ_apply {p : ℕ} (a h : Fin (p+1) → Seq) :
    freeProductDerivative (p+1) a h =
      freeExtractionDerivative (a 0) (lowerProductBand (Fin.tail a))
        (h 0,freeProductDerivative p (Fin.tail a) (Fin.tail h)) := rfl

open BTP.FreeScalar BTP.Stability
open Filter
open scoped Topology

theorem translate_preserves_cZero (k : ℕ) (v : Seq) (hv : v ∈ cZero) :
    translate k v ∈ cZero := by
  change Tendsto (fun n => v (n+k)) atTop (𝓝 0)
  exact hv.comp (tendsto_add_atTop_nat k)

theorem sequence_mul_preserves_cZero (w v : Seq) (hv : v ∈ cZero) : w*v ∈ cZero := by
  change Tendsto (fun n => w n*v n) atTop (𝓝 0)
  exact bdd_le_mul_tendsto_zero' ‖w‖
    (Eventually.of_forall (fun n => boundedSequence_abs_le w n)) hv

theorem strictCoefficientMap_preserves_cZero {m : ℕ} (R : LowerBand m)
    (hR : ∀ r, R r ∈ cZero) (d : ℕ) : strictCoefficientMap m d R ∈ cZero := by
  unfold strictCoefficientMap
  split_ifs
  · exact hR _
  · exact cZero.zero_mem

theorem freeExtractionDerivative_preserves_cZero {m : ℕ} (a : Seq) (G : LowerBand m)
    (h : Seq) (R : LowerBand m) (hh : h ∈ cZero) (hR : ∀ r, R r ∈ cZero) :
    ∀ r, freeExtractionDerivative a G (h,R) r ∈ cZero := by
  intro r
  change strictCoefficientMap m (r.val+1) R +
    bandCoefficient G r.val * translate (r.val+1) (zeroExtension 1 h) +
    translate (r.val+1) a * strictCoefficientMap m r.val R ∈ cZero
  exact cZero.add_mem (cZero.add_mem (strictCoefficientMap_preserves_cZero R hR _)
    (sequence_mul_preserves_cZero _ _ (translate_preserves_cZero _ _
      (zeroExtension_preserves_cZero 1 h hh))))
    (sequence_mul_preserves_cZero _ _ (strictCoefficientMap_preserves_cZero R hR _))

/-- The derivative descends to the quotient by sequences tending to zero
in every coefficient, as required by the general free-data necessity proof. -/
theorem freeProductDerivative_preserves_cZero (p : ℕ) (a h : Fin p → Seq)
    (hh : ∀ i, h i ∈ cZero) : ∀ r, freeProductDerivative p a h r ∈ cZero := by
  induction p with
  | zero => intro r; exact Fin.elim0 r
  | succ p ih =>
    rw [freeProductDerivative_succ_apply]
    exact freeExtractionDerivative_preserves_cZero _ _ _ _ (hh 0)
      (ih (Fin.tail a) (Fin.tail h) (fun i => hh i.succ))

#print axioms freeProduct_hasFDerivAt
#print axioms freeProductDerivative_preserves_cZero

end BTP.GeneralStability
