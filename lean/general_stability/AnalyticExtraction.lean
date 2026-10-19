import AnalyticFactorization
import Mathlib.Analysis.Calculus.FDeriv.Mul

noncomputable section
open scoped Topology

namespace BTP.GeneralStability

/-- Linear selection of a strict subdiagonal, extended by zero at the
diagonal and beyond the given bandwidth. -/
def strictCoefficientMap (m d : ℕ) : LowerBand m →L[ℝ] Seq :=
  if h : 0 < d ∧ d ≤ m then ContinuousLinearMap.proj ⟨d-1, by omega⟩ else 0

/-- A subdiagonal of a unit lower matrix, including its constant diagonal. -/
def bandCoefficient {m : ℕ} (G : LowerBand m) (d : ℕ) : Seq :=
  (if d = 0 then 1 else 0) + strictCoefficientMap m d G

@[simp] theorem strictCoefficientMap_zero (m : ℕ) : strictCoefficientMap m 0 = 0 := by
  simp [strictCoefficientMap]

@[simp] theorem bandCoefficient_zero {m : ℕ} (G : LowerBand m) :
    bandCoefficient G 0 = 1 := by simp [bandCoefficient]

@[simp] theorem bandCoefficient_coordinate {m : ℕ} (G : LowerBand m) (r : Fin m) :
    bandCoefficient G (r.val+1) = G r := by
  simp only [bandCoefficient, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
    ↓reduceIte, zero_add, strictCoefficientMap]
  have h : 0 < r.val+1 ∧ r.val+1 ≤ m := by omega
  rw [dite_eq_left h]
  congr 1

@[simp] theorem bandCoefficient_outside {m : ℕ} (G : LowerBand m) (d : ℕ) (h : m < d) :
    bandCoefficient G d = 0 := by
  have hd : d ≠ 0 := by omega
  simp [bandCoefficient, strictCoefficientMap, hd, not_le.mpr h]

theorem bandCoefficient_hasFDerivAt {m : ℕ} (G : LowerBand m) (d : ℕ) :
    HasFDerivAt (fun R : LowerBand m => bandCoefficient R d) (strictCoefficientMap m d) G := by
  have hc : HasFDerivAt (fun _ : LowerBand m => if d=0 then (1 : Seq) else 0)
      (0 : LowerBand m →L[ℝ] Seq) G := hasFDerivAt_const _ _
  have hl : HasFDerivAt (fun R : LowerBand m => strictCoefficientMap m d R)
      (strictCoefficientMap m d) G := (strictCoefficientMap m d).hasFDerivAt
  convert hc.add hl using 1 <;> first | rfl | simp only [zero_add]

/-- Multiplication of a unit lower bidiagonal by a unit lower band matrix.
The output consists of the strict subdiagonals of the genuine matrix product. -/
def leftExtraction (m : ℕ) (x : Seq × LowerBand m) : LowerBand (m+1) :=
  fun r => bandCoefficient x.2 (r.val+1) +
    translate (r.val+1) x.1 * bandCoefficient x.2 r.val

/-- Bounded derivative of `leftExtraction`: its three terms are R, HG,
and (L(a)-I)R. -/
def leftExtractionDerivative {m : ℕ} (a : Seq) (G : LowerBand m) :
    (Seq × LowerBand m) →L[ℝ] LowerBand (m+1) :=
  ContinuousLinearMap.pi fun r =>
    (strictCoefficientMap m (r.val+1)).comp (ContinuousLinearMap.snd ℝ Seq (LowerBand m)) +
    bandCoefficient G r.val •
      ((translate (r.val+1)).comp (ContinuousLinearMap.fst ℝ Seq (LowerBand m))) +
    translate (r.val+1) a •
      ((strictCoefficientMap m r.val).comp (ContinuousLinearMap.snd ℝ Seq (LowerBand m)))

theorem leftExtractionDerivative_apply {m : ℕ} (a : Seq) (G : LowerBand m)
    (h : Seq) (R : LowerBand m) (r : Fin (m+1)) (j : ℕ) :
    leftExtractionDerivative a G (h,R) r j =
      strictCoefficientMap m (r.val+1) R j +
      h (j+r.val+1) * bandCoefficient G r.val j +
      a (j+r.val+1) * strictCoefficientMap m r.val R j := by
  change (strictCoefficientMap m (r.val+1) R) j +
    (bandCoefficient G r.val * translate (r.val+1) h) j +
    (translate (r.val+1) a * strictCoefficientMap m r.val R) j = _
  simp only [BoundedContinuousFunction.mul_apply, translate_apply, Nat.add_assoc]
  ring

theorem leftExtraction_hasFDerivAt {m : ℕ} (a : Seq) (G : LowerBand m) :
    HasFDerivAt (leftExtraction m) (leftExtractionDerivative a G) (a,G) := by
  apply hasFDerivAt_pi.mpr
  intro r
  have hs (d : ℕ) : HasFDerivAt (fun x : Seq × LowerBand m => bandCoefficient x.2 d)
      ((strictCoefficientMap m d).comp (ContinuousLinearMap.snd ℝ Seq (LowerBand m))) (a,G) :=
    by
      convert (bandCoefficient_hasFDerivAt G d).comp (a,G)
        (ContinuousLinearMap.snd ℝ Seq (LowerBand m)).hasFDerivAt using 1 <;> rfl
  have ht : HasFDerivAt (fun x : Seq × LowerBand m => translate (r.val+1) x.1)
      ((translate (r.val+1)).comp (ContinuousLinearMap.fst ℝ Seq (LowerBand m))) (a,G) :=
    by
      convert (translate (r.val+1)).hasFDerivAt.comp (a,G)
        (ContinuousLinearMap.fst ℝ Seq (LowerBand m)).hasFDerivAt using 1 <;> rfl
  convert (hs (r.val+1)).add (ht.mul (hs r.val)) using 1 <;> try rfl
  apply ContinuousLinearMap.ext
  intro x
  apply BoundedContinuousFunction.ext
  intro n
  change (strictCoefficientMap m (r.val+1) x.2) n +
      (bandCoefficient G r.val * translate (r.val+1) x.1) n +
      (translate (r.val+1) a * strictCoefficientMap m r.val x.2) n =
      (strictCoefficientMap m (r.val+1) x.2) n +
      ((translate (r.val+1) a * strictCoefficientMap m r.val x.2) n +
      (bandCoefficient G r.val * translate (r.val+1) x.1) n)
  ring

#print axioms leftExtraction_hasFDerivAt
#print axioms leftExtractionDerivative_apply

end BTP.GeneralStability
