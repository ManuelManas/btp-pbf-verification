import AnalyticFactorization
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! The actual relative multiplication map, with unrestricted positive
factor growth. Its polynomial Banach-space representation uses bounded
positive weights obtained by dividing each path contribution by the
corresponding base entry. -/
noncomputable section
open Finset
open scoped Topology
namespace BTP.RelativeStability
open BTP.Stability BTP.GeneralStability

def extendRaw {p : ℕ} (a : Fin p → ℕ → ℝ) (i n : ℕ) : ℝ :=
  if hi : i<p then a ⟨i,hi⟩ n else 1

theorem extendRaw_pos {p : ℕ} (a : Fin p → ℕ → ℝ) (ha : ∀ i n,0<a i n) :
    ∀ i n,0<extendRaw a i n := by
  intro i n
  unfold extendRaw
  split_ifs with hi
  · exact ha _ _
  · exact zero_lt_one

def rawCoefficient (c : ℕ → ℕ → ℝ) : ℕ → ℕ → ℕ → ℝ
  | 0,0,_ => 1
  | 0,_+1,_ => 0
  | _k+1,0,_ => 1
  | k+1,d+1,j => rawCoefficient c k (d+1) j + rawCoefficient c k d (j+1)*c k (j+1)

theorem rawCoefficient_matrix (c : ℕ → ℕ → ℝ) (k d j : ℕ) :
    rawCoefficient c k d j=productCoefficients c k d (j+d) := by
  induction k generalizing d j with
  | zero => cases d <;> simp [rawCoefficient,productCoefficients]
  | succ k ih =>
    cases d with
    | zero => simp [rawCoefficient]
    | succ d =>
      simp only [rawCoefficient,productCoefficients,rightBidiagonal,ih]
      rw [show j+(d+1)-d=j+1 by omega,show j+1+d=j+(d+1) by omega]

theorem rawCoefficient_nonneg (c : ℕ → ℕ → ℝ) (hc : ∀ i n,0<c i n)
    (k d j : ℕ) : 0≤rawCoefficient c k d j := by
  induction k generalizing d j with
  | zero => cases d <;> simp [rawCoefficient]
  | succ k ih =>
    cases d with
    | zero => exact zero_le_one
    | succ d => exact add_nonneg (ih _ _) (mul_nonneg (ih _ _) (hc _ _).le)

theorem rawCoefficient_pos (c : ℕ → ℕ → ℝ) (hc : ∀ i n,0<c i n)
    (k d j : ℕ) (hd : d≤k) : 0<rawCoefficient c k d j := by
  induction k generalizing d j with
  | zero =>
    have : d=0 := by omega
    subst d
    exact zero_lt_one
  | succ k ih =>
    cases d with
    | zero => exact zero_lt_one
    | succ d =>
      exact add_pos_of_nonneg_of_pos (rawCoefficient_nonneg c hc k (d+1) j)
        (mul_pos (ih d (j+1) (by omega)) (hc _ _))

theorem fraction_abs_le_one {x y : ℝ} (hx : 0≤x) (hy : 0≤y) : |x/(x+y)|≤1 := by
  rw [abs_of_nonneg (div_nonneg hx (add_nonneg hx hy))]
  by_cases hz : x+y=0
  · simp [hz]
  · exact (div_le_one (lt_of_le_of_ne (add_nonneg hx hy) (Ne.symm hz))).mpr (by linarith)

theorem fraction_mul_sum {x y : ℝ} (hx : 0≤x) (hy : 0≤y) : (x+y)*(x/(x+y))=x := by
  by_cases hz : x+y=0
  · have : x=0 := by linarith
    simp [this]
  · field_simp

def leftWeight (c : ℕ → ℕ → ℝ) (hc : ∀ i n,0<c i n) (k d : ℕ) : Seq :=
  ofAbsBound (fun j => rawCoefficient c k (d+1) j/rawCoefficient c (k+1) (d+1) j) 1 (by
    intro j
    exact fraction_abs_le_one (rawCoefficient_nonneg c hc _ _ _)
      (mul_nonneg (rawCoefficient_nonneg c hc _ _ _) (hc _ _).le))

def rightWeight (c : ℕ → ℕ → ℝ) (hc : ∀ i n,0<c i n) (k d : ℕ) : Seq :=
  ofAbsBound (fun j => (rawCoefficient c k d (j+1)*c k (j+1))/rawCoefficient c (k+1) (d+1) j) 1 (by
    intro j
    have hh := fraction_abs_le_one
      (mul_nonneg (rawCoefficient_nonneg c hc k d (j+1)) (hc k (j+1)).le)
      (rawCoefficient_nonneg c hc k (d+1) j)
    simpa only [rawCoefficient,add_comm] using hh)

theorem base_mul_leftWeight (c : ℕ → ℕ → ℝ) (hc : ∀ i n,0<c i n) (k d j : ℕ) :
    rawCoefficient c (k+1) (d+1) j*leftWeight c hc k d j=rawCoefficient c k (d+1) j :=
  fraction_mul_sum (rawCoefficient_nonneg c hc _ _ _)
    (mul_nonneg (rawCoefficient_nonneg c hc _ _ _) (hc _ _).le)

theorem base_mul_rightWeight (c : ℕ → ℕ → ℝ) (hc : ∀ i n,0<c i n) (k d j : ℕ) :
    rawCoefficient c (k+1) (d+1) j*rightWeight c hc k d j=
      rawCoefficient c k d (j+1)*c k (j+1) := by
  have hh := fraction_mul_sum
    (mul_nonneg (rawCoefficient_nonneg c hc k d (j+1)) (hc k (j+1)).le)
    (rawCoefficient_nonneg c hc k (d+1) j)
  simpa only [rightWeight,ofAbsBound_apply,rawCoefficient,add_comm] using hh

def factorVariation (p i : ℕ) : FactorVariations p →L[ℝ] Seq :=
  if hi : i<p then (zeroExtension (p-i)).comp (ContinuousLinearMap.proj ⟨i,hi⟩) else 0

def relativeCoefficient (c : ℕ → ℕ → ℝ) (hc : ∀ i n,0<c i n) (p : ℕ) :
    ℕ → ℕ → FactorVariations p → Seq
  | 0,0,_ => 1
  | 0,_+1,_ => 0
  | _k+1,0,_ => 1
  | k+1,d+1,x =>
      leftWeight c hc k d * relativeCoefficient c hc p k (d+1) x +
      rightWeight c hc k d * translate 1 (relativeCoefficient c hc p k d x) *
        (1+translate 1 (factorVariation p k x))

theorem relativeCoefficient_actual (c : ℕ → ℕ → ℝ) (hc : ∀ i n,0<c i n)
    (p k d j : ℕ) (x : FactorVariations p) :
    rawCoefficient (fun i n => c i n*(1+factorVariation p i x n)) k d j =
      rawCoefficient c k d j * relativeCoefficient c hc p k d x j := by
  induction k generalizing d j with
  | zero => cases d <;> simp [rawCoefficient,relativeCoefficient]
  | succ k ih =>
    cases d with
    | zero => simp [rawCoefficient,relativeCoefficient]
    | succ d =>
      rw [rawCoefficient,ih,ih]
      simp only [relativeCoefficient,BoundedContinuousFunction.add_apply,
        BoundedContinuousFunction.mul_apply,translate_apply]
      change rawCoefficient c k (d+1) j * relativeCoefficient c hc p k (d+1) x j +
        rawCoefficient c k d (j+1)*relativeCoefficient c hc p k d x (j+1)*
        (c k (j+1)*(1+factorVariation p k x (j+1))) =
        rawCoefficient c (k+1) (d+1) j*(leftWeight c hc k d j*relativeCoefficient c hc p k (d+1) x j+
          rightWeight c hc k d j*relativeCoefficient c hc p k d x (j+1)*(1+factorVariation p k x (j+1)))
      have hleft := base_mul_leftWeight c hc k d j
      have hright := base_mul_rightWeight c hc k d j
      rw [←hleft]
      linear_combination -hright * relativeCoefficient c hc p k d x (j+1) *
        (1+factorVariation p k x (j+1))

theorem analytic_relativeCoefficient (c : ℕ → ℕ → ℝ) (hc : ∀ i n,0<c i n)
    (p k d : ℕ) (x : FactorVariations p) :
    AnalyticAt ℝ (relativeCoefficient c hc p k d) x := by
  induction k generalizing d with
  | zero => cases d <;> exact analyticAt_const
  | succ k ih =>
    cases d with
    | zero => exact analyticAt_const
    | succ d =>
      exact (analyticAt_const.mul (ih (d+1))).add
        ((analyticAt_const.mul (((translate 1).analyticAt _).comp (ih d))).mul
          (analyticAt_const.add (((translate 1).analyticAt _).comp ((factorVariation p k).analyticAt x))))

def relativeProduct {p : ℕ} (a : Fin p → ℕ → ℝ) (ha : ∀ i n,0<a i n)
    (x : FactorVariations p) : LowerBand p :=
  fun r => relativeCoefficient (extendRaw a) (extendRaw_pos a ha) p p (r.val+1) x-1

theorem analytic_relativeProduct {p : ℕ} (a : Fin p → ℕ → ℝ) (ha : ∀ i n,0<a i n)
    (x : FactorVariations p) : AnalyticAt ℝ (relativeProduct a ha) x := by
  apply AnalyticAt.pi
  intro r
  exact (analytic_relativeCoefficient _ _ p p (r.val+1) x).sub analyticAt_const

theorem relativeProduct_actual {p : ℕ} (a : Fin p → ℕ → ℝ) (ha : ∀ i n,0<a i n)
    (x : FactorVariations p) (r : Fin p) (j : ℕ) :
    relativeProduct a ha x r j =
      (rawCoefficient (fun i n => extendRaw a i n*(1+factorVariation p i x n)) p (r.val+1) j -
        rawCoefficient (extendRaw a) p (r.val+1) j)/rawCoefficient (extendRaw a) p (r.val+1) j := by
  rw [relativeCoefficient_actual _ (extendRaw_pos a ha)]
  have hz := ne_of_gt (rawCoefficient_pos (extendRaw a) (extendRaw_pos a ha) p (r.val+1) j (by omega))
  simp only [relativeProduct,BoundedContinuousFunction.sub_apply,
    BoundedContinuousFunction.coe_one,Pi.one_apply]
  field_simp

@[simp] theorem relativeProduct_zero {p : ℕ} (a : Fin p → ℕ → ℝ) (ha : ∀ i n,0<a i n) :
    relativeProduct a ha 0=0 := by
  funext r
  apply BoundedContinuousFunction.ext
  intro j
  rw [relativeProduct_actual]
  have he : (fun i n => extendRaw a i n*(1+factorVariation p i 0 n))=extendRaw a := by
    funext i n
    simp
  rw [he]
  simp

def relativeCoefficientDerivative (c : ℕ → ℕ → ℝ) (hc : ∀ i n,0<c i n) (p : ℕ)
    (x : FactorVariations p) : ℕ → ℕ → FactorVariations p →L[ℝ] Seq
  | 0,_ => 0
  | _k+1,0 => 0
  | k+1,d+1 =>
      leftWeight c hc k d • relativeCoefficientDerivative c hc p x k (d+1) +
      (rightWeight c hc k d * translate 1 (relativeCoefficient c hc p k d x)) •
        ((translate 1).comp (factorVariation p k)) +
      (1+translate 1 (factorVariation p k x)) •
        (rightWeight c hc k d • ((translate 1).comp (relativeCoefficientDerivative c hc p x k d)))

theorem relativeCoefficient_hasFDerivAt (c : ℕ → ℕ → ℝ) (hc : ∀ i n,0<c i n)
    (p k d : ℕ) (x : FactorVariations p) :
    HasFDerivAt (relativeCoefficient c hc p k d) (relativeCoefficientDerivative c hc p x k d) x := by
  induction k generalizing d with
  | zero => cases d <;> exact hasFDerivAt_const _ _
  | succ k ih =>
    cases d with
    | zero => exact hasFDerivAt_const _ _
    | succ d =>
      have hl := (ih (d+1)).const_mul (leftWeight c hc k d)
      have hg := ((translate 1).hasFDerivAt.comp x (ih d)).const_mul (rightWeight c hc k d)
      have hv := (hasFDerivAt_const (1 : Seq) x).add
        ((translate 1).hasFDerivAt.comp x (factorVariation p k).hasFDerivAt)
      convert hl.add (hg.mul hv) using 1 <;>
        first | rfl | simp only [relativeCoefficientDerivative,zero_add,add_assoc,
          Function.comp_apply,Pi.add_apply]

def relativeProductDerivative {p : ℕ} (a : Fin p → ℕ → ℝ) (ha : ∀ i n,0<a i n)
    (x : FactorVariations p) : FactorVariations p →L[ℝ] LowerBand p :=
  ContinuousLinearMap.pi fun r =>
    relativeCoefficientDerivative (extendRaw a) (extendRaw_pos a ha) p x p (r.val+1)

theorem relativeProduct_hasFDerivAt {p : ℕ} (a : Fin p → ℕ → ℝ) (ha : ∀ i n,0<a i n)
    (x : FactorVariations p) :
    HasFDerivAt (relativeProduct a ha) (relativeProductDerivative a ha x) x := by
  apply hasFDerivAt_pi.mpr
  intro r
  have hh := (relativeCoefficient_hasFDerivAt (extendRaw a) (extendRaw_pos a ha) p p (r.val+1) x).sub
    (hasFDerivAt_const (1 : Seq) x)
  change HasFDerivAt (fun y => relativeCoefficient (extendRaw a) (extendRaw_pos a ha) p p (r.val+1) y - 1)
    _ x
  convert hh using 1 <;> first | rfl | simp only [sub_zero]

#print axioms relativeCoefficient_actual
#print axioms analytic_relativeProduct
#print axioms relativeProduct_hasFDerivAt

end BTP.RelativeStability
