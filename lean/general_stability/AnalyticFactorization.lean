import ExtractionDerivative
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Tactic

/-! Analytic local factorization: inverse and section arguments in real Banach
spaces, together with the actual polynomial multiplication of band factors.
The matrix realization is added below the general analytic lemmas. -/

noncomputable section
open Filter
open scoped Topology

namespace BTP.AnalyticFactorization

section Inverse

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace E] [CompleteSpace F]

omit [CompleteSpace F] in
/-- Analytic Banach inverse theorem with both local inverse identities and
the prescribed value at the base point. -/
theorem analytic_local_inverse {f : E → F} {a : E}
    (hf : AnalyticAt ℝ f a) (D : E ≃L[ℝ] F)
    (hD : HasFDerivAt f (D : E →L[ℝ] F) a) :
    ∃ g : F → E, AnalyticAt ℝ g (f a) ∧ g (f a) = a ∧
      (∀ᶠ y in 𝓝 (f a), f (g y) = y) ∧
      (∀ᶠ x in 𝓝 a, g (f x) = x) := by
  have hs : HasStrictFDerivAt f (D : E →L[ℝ] F) a := by
    simpa only [hD.fderiv] using hf.hasStrictFDerivAt
  let H := hs.toOpenPartialHomeomorph f
  have hHa : a ∈ H.source := hs.mem_toOpenPartialHomeomorph_source
  have hHan : AnalyticAt ℝ H a := hf
  have hHderiv : fderiv ℝ H a = (D : E →L[ℝ] F) := hD.fderiv
  have hginv : AnalyticAt ℝ H.symm (f a) :=
    H.analyticAt_symm' hHa hHan hHderiv
  refine ⟨hs.localInverse f D a, hginv, hs.localInverse_apply_image,
    hs.eventually_right_inverse, hs.eventually_left_inverse⟩

omit [CompleteSpace E] [CompleteSpace F] in
/-- A local differentiable section forces a bounded right inverse of the
derivative. The derivative identity is proved by the chain rule. -/
theorem derivative_right_inverse_of_section {f : E → F} {g : F → E} {a : E}
    {A : E →L[ℝ] F} {B : F →L[ℝ] E}
    (hf : HasFDerivAt f A a) (hg : HasFDerivAt g B (f a))
    (hga : g (f a) = a) (hsection : ∀ᶠ y in 𝓝 (f a), f (g y) = y) :
    A.comp B = ContinuousLinearMap.id ℝ F := by
  have hfa : HasFDerivAt f A (g (f a)) := by rwa [hga]
  have hcomp := hfa.comp (f a) hg
  have hid : HasFDerivAt (fun y => f (g y)) (ContinuousLinearMap.id ℝ F) (f a) :=
    (hasFDerivAt_id (f a)).congr_of_eventuallyEq hsection
  exact hcomp.unique hid

omit [CompleteSpace E] in
/-- A bounded linear right inverse of the derivative yields an analytic
local section. The construction restricts the original map to the affine
subspace `a + range B` and applies the inverse theorem there. -/
theorem analytic_local_section {f : E → F} {a : E}
    (hf : AnalyticAt ℝ f a) (A : E →L[ℝ] F) (B : F →L[ℝ] E)
    (hA : HasFDerivAt f A a) (hAB : A.comp B = ContinuousLinearMap.id ℝ F) :
    ∃ g : F → E, AnalyticAt ℝ g (f a) ∧ g (f a) = a ∧
      (∀ᶠ y in 𝓝 (f a), f (g y) = y) := by
  let H : F → F := fun v => f (a + B v)
  have hzero : a + B 0 = a := by simp
  have hinner : AnalyticAt ℝ (fun v : F => a + B v) 0 :=
    analyticAt_const.add (B.analyticAt 0)
  have hH : AnalyticAt ℝ H 0 :=
    (hf.comp_of_eq hinner hzero)
  have hiD : HasFDerivAt (fun v : F => a + B v) B 0 := by
    convert (hasFDerivAt_const a (0 : F)).add B.hasFDerivAt using 1
    · rfl
    · rw [zero_add]
  have hHD : HasFDerivAt H (ContinuousLinearMap.id ℝ F) 0 := by
    have hAf : HasFDerivAt f A (a + B 0) := by simpa only [hzero] using hA
    simpa only [hAB, H, Function.comp_def] using hAf.comp (0 : F) hiD
  obtain ⟨h, hh, hh0, hright, _⟩ := analytic_local_inverse hH
    (ContinuousLinearEquiv.refl ℝ F) hHD
  have hH0 : H 0 = f a := by simp [H]
  refine ⟨fun y => a + B (h y), ?_, ?_, ?_⟩
  · exact analyticAt_const.add ((B.analyticAt (h (f a))).comp
      (f := h) (by simpa only [hH0] using hh))
  · have hh0' : h (f a) = 0 := by simpa only [hH0] using hh0
    simp [hh0']
  · simpa only [hH0, H] using hright

end Inverse

end BTP.AnalyticFactorization

namespace BTP.GeneralStability

/-- Forward translation of a bounded sequence. The factor entries are
indexed by row, whereas band coefficients are indexed by column. -/
def translate (k : ℕ) : Seq →L[ℝ] Seq :=
  BoundedContinuousFunction.compContinuousCLM ℝ ℝ
    ⟨fun n : ℕ => n + k, continuous_of_discreteTopology⟩

@[simp] theorem translate_apply (k : ℕ) (a : Seq) (n : ℕ) :
    translate k a n = a (n + k) := rfl

/-- Zero extension from the first free row, as a bounded linear map. -/
def zeroExtension (first : ℕ) : Seq →L[ℝ] Seq :=
  let A : Seq →ₗ[ℝ] Seq :=
    { toFun := fun h => BTP.Stability.ofAbsBound (initialExtension first h) ‖h‖ (by
        intro n
        unfold initialExtension
        split_ifs
        · exact BTP.Stability.boundedSequence_abs_le h _
        · simp)
      map_add' := by
        intro h k
        apply BoundedContinuousFunction.ext
        intro n
        change initialExtension first (h+k) n =
          initialExtension first h n + initialExtension first k n
        unfold initialExtension
        split_ifs <;> simp
      map_smul' := by
        intro c h
        apply BoundedContinuousFunction.ext
        intro n
        change initialExtension first (c • h) n = c * initialExtension first h n
        unfold initialExtension
        split_ifs <;> simp }
  A.mkContinuous 1 (by
    intro h
    apply BoundedContinuousFunction.norm_le_of_nonempty.mpr
    intro n
    change |initialExtension first h n| ≤ 1 * ‖h‖
    simp only [one_mul, initialExtension]
    split_ifs
    · exact BTP.Stability.boundedSequence_abs_le h _
    · simp)

@[simp] theorem zeroExtension_apply (first : ℕ) (h : Seq) (n : ℕ) :
    zeroExtension first h n = initialExtension first h n := rfl

/-- Coefficient of subdiagonal `d` in a product of unit lower bidiagonals.
The sequence coordinate is the column; no fictitious entries above row zero
occur. Factor lists are ordered from left to right. -/
def productCoefficient : List Seq → ℕ → Seq
  | [], 0 => 1
  | [], _ + 1 => 0
  | _ :: _, 0 => 1
  | a :: as, d + 1 => productCoefficient as (d+1) +
      translate (d+1) a * productCoefficient as d

@[simp] theorem productCoefficient_zero (as : List Seq) :
    productCoefficient as 0 = 1 := by cases as <;> rfl

theorem productCoefficient_outside (as : List Seq) (d : ℕ) (hd : as.length < d) :
    productCoefficient as d = 0 := by
  induction as generalizing d with
  | nil => cases d <;> simp_all [productCoefficient]
  | cons a as ih =>
    cases d with
    | zero => simp_all
    | succ d =>
      simp only [List.length_cons] at hd
      have h1 : as.length < d := by omega
      simp only [productCoefficient, ih _ h1, ih _ (by omega : as.length < d+1),
        mul_zero, add_zero]

/-- Appending one factor on the right gives the same coefficient law as
ordinary lower-bidiagonal matrix multiplication. -/
theorem productCoefficient_append (as : List Seq) (b : Seq) (d j : ℕ) :
    productCoefficient (as ++ [b]) (d+1) j =
      productCoefficient as (d+1) j + productCoefficient as d (j+1) * b (j+1) := by
  induction as generalizing d j with
  | nil =>
    cases d <;> simp [productCoefficient, translate_apply]
  | cons a as ih =>
    cases d with
    | zero => simp [productCoefficient, ih, translate_apply]; ring
    | succ d =>
      simp only [List.cons_append, productCoefficient, BoundedContinuousFunction.add_apply,
        BoundedContinuousFunction.mul_apply, translate_apply, ih]
      simp only [show j+1+(d+1) = j+(d+1+1) by omega]
      ring

/-- Strict subdiagonals of the actual product of the supplied factors. -/
def lowerProductBand {p : ℕ} (a : Fin p → Seq) : LowerBand p :=
  fun r => productCoefficient (List.ofFn a) (r.val+1)

/-- Multiplication with all prescribed initial entries held fixed. -/
def fixedProduct {p : ℕ} (a : Fin p → Seq) (h : FactorVariations p) : LowerBand p :=
  lowerProductBand (fun i => a i + zeroExtension (p-i.val) (h i))

@[simp] theorem fixedProduct_zero {p : ℕ} (a : Fin p → Seq) :
    fixedProduct a 0 = lowerProductBand a := by
  simp only [fixedProduct, Pi.zero_apply, map_zero, add_zero]

theorem fixedProduct_factor_entries {p : ℕ} (a : Fin p → Seq)
    (h : FactorVariations p) (i : Fin p) (n : ℕ) :
    (a i + zeroExtension (p-i.val) (h i)) n = perturbedFactors a h i n := rfl

section AnalyticProduct

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem analytic_productCoefficient (fs : List (E → Seq)) {x : E}
    (hf : ∀ f ∈ fs, AnalyticAt ℝ f x) (d : ℕ) :
    AnalyticAt ℝ (fun y => productCoefficient (fs.map (fun f => f y)) d) x := by
  induction fs generalizing d with
  | nil => cases d <;> exact analyticAt_const
  | cons f fs ih =>
    have hhead : AnalyticAt ℝ f x := hf f (by simp)
    have htail : ∀ g ∈ fs, AnalyticAt ℝ g x := fun g hg => hf g (by simp [hg])
    cases d with
    | zero => exact analyticAt_const
    | succ d =>
      exact (ih htail (d+1)).add
        (((translate (d+1)).analyticAt (f x)).comp hhead |>.mul (ih htail d))

theorem analytic_lowerProductBand (p : ℕ) (x : Fin p → Seq) :
    AnalyticAt ℝ (@lowerProductBand p) x := by
  apply AnalyticAt.pi
  intro r
  let fs : List ((Fin p → Seq) → Seq) := List.ofFn (fun i => fun a => a i)
  have hf : ∀ f ∈ fs, AnalyticAt ℝ f x := by
    intro f hmem
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hmem
    exact (ContinuousLinearMap.proj (R := ℝ) i).analyticAt x
  have h := analytic_productCoefficient fs hf (r.val+1)
  simpa only [fs, List.map_ofFn, Function.comp_def, lowerProductBand] using h

theorem analytic_fixedProduct (p : ℕ) (a : Fin p → Seq) (x : FactorVariations p) :
    AnalyticAt ℝ (fixedProduct a) x := by
  have hinner : AnalyticAt ℝ
      (fun h : FactorVariations p => fun i => a i + zeroExtension (p-i.val) (h i)) x := by
    apply AnalyticAt.pi
    intro i
    exact analyticAt_const.add (((zeroExtension (p-i.val)).analyticAt (x i)).comp
      (f := fun h : FactorVariations p => h i)
      ((ContinuousLinearMap.proj (R := ℝ) i).analyticAt x))
  exact (analytic_lowerProductBand p _).comp hinner

end AnalyticProduct

end BTP.GeneralStability
