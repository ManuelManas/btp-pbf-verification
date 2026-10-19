import AnalyticExtraction
import AnalyticMatrixRealization
import Mathlib.Analysis.Normed.Operator.Mul

/-! First-order factors on the Banach space of bounded sequences. -/

noncomputable section
namespace BTP.GeneralStability
open BTP.Stability

/-- The reciprocal of a bounded positive sequence bounded away from zero. -/
def positiveReciprocal (d : Seq) (α : ℝ) (hα : 0 < α) (hd : ∀ n, α ≤ d n) : Seq :=
  ofAbsBound (fun n => 1 / d n) (1 / α) (by
    intro n
    have hdn : 0 < d n := lt_of_lt_of_le hα (hd n)
    rw [abs_of_pos (one_div_pos.mpr hdn)]
    exact one_div_le_one_div_of_le hα (hd n))

@[simp] theorem positiveReciprocal_apply (d : Seq) (α : ℝ) (hα : 0 < α)
    (hd : ∀ n, α ≤ d n) (n : ℕ) : positiveReciprocal d α hα hd n = 1 / d n := rfl

/-- Multiplication by a uniformly positive bounded sequence is a Banach
space isomorphism, with its pointwise reciprocal as the inverse. -/
def diagonalEquiv (d : Seq) (α : ℝ) (hα : 0 < α) (hd : ∀ n, α ≤ d n) : Seq ≃L[ℝ] Seq where
  toLinearEquiv :=
    { toLinearMap := (ContinuousLinearMap.mul ℝ Seq d).toLinearMap
      invFun := fun f => positiveReciprocal d α hα hd * f
      left_inv := by
        intro f
        apply BoundedContinuousFunction.ext
        intro n
        change (1/d n)*(d n*f n) = f n
        have hn : d n ≠ 0 := ne_of_gt (lt_of_lt_of_le hα (hd n))
        field_simp
      right_inv := by
        intro f
        apply BoundedContinuousFunction.ext
        intro n
        change d n*((1/d n)*f n) = f n
        have hn : d n ≠ 0 := ne_of_gt (lt_of_lt_of_le hα (hd n))
        field_simp }
  continuous_toFun := (ContinuousLinearMap.mul ℝ Seq d).continuous
  continuous_invFun := (ContinuousLinearMap.mul ℝ Seq (positiveReciprocal d α hα hd)).continuous

/-- The first-order operator with diagonal d and negative weighted shift a.
At index zero its value is d(0)h(0), with preceding initial value zero. -/
def firstOrderMap (a d : Seq) : Seq →L[ℝ] Seq :=
  ContinuousLinearMap.mul ℝ Seq d + differenceMap a - ContinuousLinearMap.id ℝ Seq

@[simp] theorem firstOrderMap_zero (a d h : Seq) : firstOrderMap a d h 0 = d 0*h 0 := by
  change d 0*h 0+h 0-h 0 = _
  ring

@[simp] theorem firstOrderMap_succ (a d h : Seq) (n : ℕ) :
    firstOrderMap a d h (n+1) = d (n+1)*h (n+1)-a (n+1)*h n := by
  change d (n+1)*h (n+1)+(h (n+1)-a (n+1)*h n)-h (n+1) = _
  ring

/-- Exact normalization of every first-order extraction operator. -/
theorem firstOrderMap_normalization (a d : Seq) (α : ℝ) (hα : 0 < α)
    (hd : ∀ n, α ≤ d n) :
    firstOrderMap a d =
      (diagonalEquiv d α hα hd).toContinuousLinearMap.comp
        (differenceMap (a * positiveReciprocal d α hα hd)) := by
  apply ContinuousLinearMap.ext
  intro h
  apply BoundedContinuousFunction.ext
  intro n
  cases n with
  | zero => exact firstOrderMap_zero a d h
  | succ n =>
    rw [firstOrderMap_succ]
    change d (n+1)*h (n+1)-a (n+1)*h n =
      d (n+1)*(h (n+1)-(a (n+1)*(1/d (n+1)))*h n)
    have hn : d (n+1) ≠ 0 := ne_of_gt (lt_of_lt_of_le hα (hd (n+1)))
    field_simp

/-- The first-order extraction operator is injective even without a
geometric assumption: the first row and then the recurrence determine h. -/
theorem firstOrderMap_injective (a d : Seq) (hd : ∀ n, d n ≠ 0) :
    Function.Injective (firstOrderMap a d) := by
  intro h k he
  apply BoundedContinuousFunction.ext
  intro n
  induction n with
  | zero =>
    have hh := congrArg (fun f : Seq => f 0) he
    simp only [firstOrderMap_zero] at hh
    exact (mul_left_cancel₀ (hd 0)) hh
  | succ n ih =>
    have hh := congrArg (fun f : Seq => f (n+1)) he
    simp only [firstOrderMap_succ, ih] at hh
    exact (mul_left_cancel₀ (hd (n+1))) (by linarith)

/-- Necessary and sufficient scalar criterion for an arbitrary extraction
factor, derived from the actual operator normalization. -/
theorem firstOrderMap_bijective_iff_geometric (a d : Seq) (ha : ∀ n, 0 ≤ a n)
    (α : ℝ) (hα : 0 < α) (hd : ∀ n, α ≤ d n) :
    Function.Bijective (firstOrderMap a d) ↔
      ∃ C ρ : ℝ, 1 ≤ C ∧ 0 < ρ ∧ ρ < 1 ∧
        ∀ s N, blockProduct (fun n => a n/d n) s N ≤ C*ρ^N := by
  have he := firstOrderMap_normalization a d α hα hd
  let γ := a * positiveReciprocal d α hα hd
  have hγ : ∀ n, 0 ≤ γ n := by
    intro n
    change 0 ≤ a n*(1/d n)
    exact mul_nonneg (ha n) (one_div_nonneg.mpr (le_trans hα.le (hd n)))
  have hnorm : Function.Bijective (firstOrderMap a d) ↔ Function.Bijective (differenceMap γ) := by
    rw [he]
    constructor
    · intro hb
      refine ⟨?_, ?_⟩
      · intro f g hfg
        apply hb.1
        exact congrArg (diagonalEquiv d α hα hd) hfg
      · intro y
        obtain ⟨x, hx⟩ := hb.2 (diagonalEquiv d α hα hd y)
        refine ⟨x, ?_⟩
        exact (diagonalEquiv d α hα hd).injective hx
    · intro hb
      exact (diagonalEquiv d α hα hd).bijective.comp hb
  rw [hnorm, differenceMap_bijective_iff_geometric γ hγ]
  have heq : (γ : ℕ → ℝ) = fun n => a n / d n := by
    funext n
    change a n*(1/d n) = a n/d n
    ring
  rw [heq]

/-- A product of injective endomorphisms is bijective precisely when all
its factors are. This is applied to the proved injectivity of D_j. -/
theorem composition_bijective_iff {X : Type*} (F : List (X → X))
    (hF : ∀ f ∈ F, Function.Injective f) :
    Function.Bijective (F.foldl (fun g f => f ∘ g) id) ↔
      ∀ f ∈ F, Function.Bijective f := by
  induction F using List.reverseRecOn with
  | nil => simpa using Function.bijective_id
  | append_singleton F f ih =>
    have hfinj : Function.Injective f := hF f (by simp)
    have hFinj : ∀ g ∈ F, Function.Injective g := fun g hg => hF g (by simp [hg])
    have hi := ih hFinj
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
    constructor
    · intro hb
      have hfsur : Function.Surjective f := hb.2.of_comp
      have hfb : Function.Bijective f := ⟨hfinj, hfsur⟩
      have hrest : Function.Bijective (F.foldl (fun g f => f ∘ g) id) := by
        refine ⟨hb.1.of_comp, ?_⟩
        intro y
        obtain ⟨x,hx⟩ := hb.2 (f y)
        exact ⟨x,hfinj hx⟩
      intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · exact (hi.mp hrest) g hg
      · have he : g = f := List.mem_singleton.mp hg
        subst g
        exact hfb
    · intro hb
      have hfb := hb f (by simp)
      have hrest := hi.mpr (fun g hg => hb g (by simp [hg]))
      exact hfb.comp hrest

/-- Elimination down the subdiagonals, with the column index fixed. All
operations take place in the Banach space of bounded sequences. -/
def eliminationMap (a : Seq) (width : ℕ) : ℕ → LowerBand width →L[ℝ] Seq
  | 0 => 0
  | s+1 => strictCoefficientMap width (s+1) - translate (s+1) a • eliminationMap a width s

/-- The scalar residual produced by varying the first factor, with its
first `m` subdiagonal entries held fixed. -/
def residualMap {m : ℕ} (a : Seq) (G : LowerBand m) : ℕ → Seq →L[ℝ] Seq
  | 0 => 0
  | s+1 => bandCoefficient G s • ((translate (s+1)).comp (zeroExtension (m+1))) -
      translate (s+1) a • residualMap a G s

/-- The genuine extraction derivative restricted to the prescribed initial
entries, rather than to unrestricted variations of the first factor. -/
def fixedExtractionDerivative {m : ℕ} (a : Seq) (G : LowerBand m) :
    (Seq × LowerBand m) →L[ℝ] LowerBand (m+1) :=
  (leftExtractionDerivative a G).comp
    ((zeroExtension (m+1)).prodMap (ContinuousLinearMap.id ℝ (LowerBand m)))

@[simp] theorem strictCoefficientMap_coordinate {m : ℕ} (R : LowerBand m) (r : Fin m) :
    strictCoefficientMap m (r.val+1) R = R r := by
  have h := bandCoefficient_coordinate R r
  simpa [bandCoefficient] using h

@[simp] theorem strictCoefficientMap_outside (m d : ℕ) (h : m < d) :
    strictCoefficientMap m d = 0 := by
  simp [strictCoefficientMap, not_le.mpr h]

@[simp] theorem eliminationMap_zero (a : Seq) (w : ℕ) : eliminationMap a w 0 = 0 := rfl
@[simp] theorem residualMap_zero {m : ℕ} (a : Seq) (G : LowerBand m) : residualMap a G 0 = 0 := rfl

theorem eliminationMap_succ (a : Seq) (w s : ℕ) (E : LowerBand w) (j : ℕ) :
    eliminationMap a w (s+1) E j = strictCoefficientMap w (s+1) E j -
      a (j+s+1)*eliminationMap a w s E j := by
  simp [eliminationMap, Nat.add_assoc]

theorem residualMap_succ {m : ℕ} (a : Seq) (G : LowerBand m) (s : ℕ) (h : Seq) (j : ℕ) :
    residualMap a G (s+1) h j =
      initialExtension (m+1) h (j+s+1)*bandCoefficient G s j -
      a (j+s+1)*residualMap a G s h j := by
  simp [residualMap, Nat.add_assoc, mul_comm]

theorem fixedExtractionDerivative_coordinate {m : ℕ} (a : Seq) (G : LowerBand m)
    (h : Seq) (R : LowerBand m) (r : Fin (m+1)) (j : ℕ) :
    fixedExtractionDerivative a G (h,R) r j =
      strictCoefficientMap m (r.val+1) R j +
      initialExtension (m+1) h (j+r.val+1)*bandCoefficient G r.val j +
      a (j+r.val+1)*strictCoefficientMap m r.val R j := by
  change leftExtractionDerivative a G (zeroExtension (m+1) h,R) r j = _
  rw [leftExtractionDerivative_apply, zeroExtension_apply]

/-- Triangularization of the extraction derivative. In the final
subdiagonal the remainder vanishes, leaving precisely the scalar residual. -/
theorem elimination_fixedExtraction {m : ℕ} (a : Seq) (G : LowerBand m)
    (h : Seq) (R : LowerBand m) (s : ℕ) (hs : s ≤ m+1) :
    eliminationMap a (m+1) s (fixedExtractionDerivative a G (h,R)) =
      residualMap a G s h + strictCoefficientMap m s R := by
  induction s with
  | zero => simp
  | succ s ih =>
    have ih' := ih (by omega)
    apply BoundedContinuousFunction.ext
    intro j
    rw [eliminationMap_succ, strictCoefficientMap_coordinate _ ⟨s,by omega⟩,
      fixedExtractionDerivative_coordinate, ih']
    change _ = residualMap a G (s+1) h j + strictCoefficientMap m (s+1) R j
    rw [residualMap_succ]
    simp only [BoundedContinuousFunction.add_apply]
    ring

/-- The bounded lower-band remainder obtained by elimination. -/
def extractionRemainder {m : ℕ} (a : Seq) (G : LowerBand m)
    (h : Seq) (E : LowerBand (m+1)) : LowerBand m :=
  fun r => eliminationMap a (m+1) (r.val+1) E - residualMap a G (r.val+1) h

/-- All lower coefficient equations and the final scalar equation give
exactly the derivative equation for the actual matrix product. -/
theorem fixedExtraction_solves {m : ℕ} (a : Seq) (G : LowerBand m)
    (h : Seq) (E : LowerBand (m+1))
    (htop : residualMap a G (m+1) h = eliminationMap a (m+1) (m+1) E) :
    fixedExtractionDerivative a G (h,extractionRemainder a G h E) = E := by
  let R := extractionRemainder a G h E
  have hR (s : ℕ) (hs : s ≤ m+1) :
      strictCoefficientMap m s R = eliminationMap a (m+1) s E - residualMap a G s h := by
    by_cases hz : s=0
    · subst s; simp
    by_cases hsm : s ≤ m
    · have hp : 0<s := by omega
      obtain ⟨t,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hz
      exact strictCoefficientMap_coordinate R ⟨t,by omega⟩
    · have he : s=m+1 := by omega
      subst s
      rw [strictCoefficientMap_outside m (m+1) (by omega)]
      simp [htop]
  funext r
  apply BoundedContinuousFunction.ext
  intro j
  rw [fixedExtractionDerivative_coordinate, hR (r.val+1) (by omega), hR r.val (by omega)]
  simp only [BoundedContinuousFunction.sub_apply]
  rw [eliminationMap_succ, residualMap_succ]
  rw [strictCoefficientMap_coordinate E r]
  ring

/-- Elimination is injective when all subdiagonal outputs are retained. -/
theorem elimination_determines {m : ℕ} (a : Seq) (E F : LowerBand m)
    (he : ∀ s, s ≤ m → eliminationMap a m s E = eliminationMap a m s F) : E=F := by
  funext r
  apply BoundedContinuousFunction.ext
  intro j
  have ht := congrArg (fun f : Seq => f j) (he (r.val+1) (by omega))
  rw [eliminationMap_succ, eliminationMap_succ, strictCoefficientMap_coordinate E r,
    strictCoefficientMap_coordinate F r, he r.val (by omega)] at ht
  linarith

/-- Every scalar forcing sequence is realized by a matrix variation
supported on its last subdiagonal. -/
def deepestBand (m : ℕ) (f : Seq) : LowerBand (m+1) :=
  fun r => if r.val=m then f else 0

theorem elimination_deepest {m : ℕ} (a f : Seq) :
    eliminationMap a (m+1) (m+1) (deepestBand m f) = f := by
  have hz (s : ℕ) (hs : s ≤ m) : eliminationMap a (m+1) s (deepestBand m f) = 0 := by
    induction s with
    | zero => rfl
    | succ s ih =>
      have hh := ih (by omega)
      apply BoundedContinuousFunction.ext
      intro j
      rw [eliminationMap_succ, hh, strictCoefficientMap_coordinate _ ⟨s,by omega⟩]
      simp [deepestBand, show s ≠ m by omega]
  apply BoundedContinuousFunction.ext
  intro j
  rw [eliminationMap_succ, hz m (le_refl _),
    strictCoefficientMap_coordinate _ ⟨m,by omega⟩]
  simp [deepestBand]

/-- The full derivative for lower-band extraction is bijective if and
only if its scalar eliminated equation is bijective. -/
theorem fixedExtraction_bijective_iff {m : ℕ} (a : Seq) (G : LowerBand m) :
    Function.Bijective (fixedExtractionDerivative a G) ↔
      Function.Bijective (residualMap a G (m+1)) := by
  constructor
  · intro hb
    constructor
    · intro h k he
      let E := deepestBand m (residualMap a G (m+1) h)
      have hh : residualMap a G (m+1) h = eliminationMap a (m+1) (m+1) E :=
        (elimination_deepest a _).symm
      have hk : residualMap a G (m+1) k = eliminationMap a (m+1) (m+1) E := by
        rw [←he]; exact hh
      have hv := hb.1 ((fixedExtraction_solves a G h E hh).trans
        (fixedExtraction_solves a G k E hk).symm)
      exact congrArg Prod.fst hv
    · intro f
      obtain ⟨⟨h,R⟩,hx⟩ := hb.2 (deepestBand m f)
      refine ⟨h,?_⟩
      have hh := elimination_fixedExtraction a G h R (m+1) (le_refl _)
      rw [hx, elimination_deepest, strictCoefficientMap_outside m (m+1) (by omega)] at hh
      simpa using hh.symm
  · intro hb
    constructor
    · intro x y he
      rcases x with ⟨h,R⟩
      rcases y with ⟨k,S⟩
      have ht := congrArg (eliminationMap a (m+1) (m+1)) he
      rw [elimination_fixedExtraction, elimination_fixedExtraction,
        strictCoefficientMap_outside m (m+1) (by omega)] at ht
      have hhk : h=k := hb.1 (by simpa using ht)
      subst k
      have hrs : R=S := by
        funext r
        have ht := congrArg (eliminationMap a (m+1) (r.val+1)) he
        rw [elimination_fixedExtraction _ _ _ _ _ (by omega),
          elimination_fixedExtraction _ _ _ _ _ (by omega)] at ht
        simpa only [strictCoefficientMap_coordinate] using add_left_cancel ht
      subst S
      rfl
      all_goals omega
    · intro E
      obtain ⟨h,hh⟩ := hb.2 (eliminationMap a (m+1) (m+1) E)
      exact ⟨(h,extractionRemainder a G h E), fixedExtraction_solves a G h E hh⟩

#print axioms fixedExtraction_bijective_iff

/-- The first-order factors of the scalar extraction equation, after
removing the fixed initial rows. -/
def shiftedFirstOrder (m k : ℕ) (a : Seq) (b : ℕ → Seq) : Seq →L[ℝ] Seq :=
  firstOrderMap (translate (m+1) a) (translate (m-k) (b k))

def shiftedFirstOrderComposition (m : ℕ) (a : Seq) (b : ℕ → Seq) : ℕ → Seq →L[ℝ] Seq
  | 0 => ContinuousLinearMap.id ℝ Seq
  | k+1 => (shiftedFirstOrder m k a b).comp (shiftedFirstOrderComposition m a b k)

theorem firstOrderProduct_initial_zero (m : ℕ) (a : Seq) (b : ℕ → Seq) (h : Seq)
    (k n : ℕ) (hn : n < m+1) :
    firstOrderProduct a (fun i n => b i n) (initialExtension (m+1) h) k n = 0 := by
  induction k generalizing n with
  | zero => simp [firstOrderProduct, initialExtension, show ¬m+1≤n by omega]
  | succ k ih => simp [firstOrderProduct, ih n hn, ih (n-1) (by omega)]

/-- Identification with the exact scalar product obtained from matrix
elimination, including the first-row boundary condition. -/
theorem shiftedFirstOrderComposition_apply (m : ℕ) (a : Seq) (b : ℕ → Seq)
    (h : Seq) (k : ℕ) (hk : k ≤ m) (n : ℕ) :
    shiftedFirstOrderComposition m a b k h n =
      firstOrderProduct a (fun i n => b i n) (initialExtension (m+1) h) k (n+m+1) := by
  induction k generalizing n with
  | zero => simp [shiftedFirstOrderComposition, firstOrderProduct, initialExtension]
  | succ k ih =>
    have hkm : k≤m := by omega
    cases n with
    | zero =>
      change firstOrderMap (translate (m+1) a) (translate (m-k) (b k))
        (shiftedFirstOrderComposition m a b k h) 0 = _
      rw [firstOrderMap_zero, ih hkm]
      simp only [translate_apply, zero_add, firstOrderProduct]
      rw [show m+1-1=m by omega, firstOrderProduct_initial_zero m a b h k m (by omega)]
      have he : m+1-(k+1)=m-k := by omega
      simp [he]
    | succ n =>
      change firstOrderMap (translate (m+1) a) (translate (m-k) (b k))
        (shiftedFirstOrderComposition m a b k h) (n+1) = _
      rw [firstOrderMap_succ, ih hkm, ih hkm]
      simp only [translate_apply, firstOrderProduct]
      have he : n+1+m+1-(k+1)=n+1+(m-k) := by omega
      have he' : n+1+m+1-1=n+m+1 := by omega
      rw [he, he']
      congr 2

/-- Necessary and sufficient geometric conditions for all factors of the
scalar extraction operator, with no commutation of these operators. -/
theorem shiftedFirstOrderComposition_bijective_iff (m : ℕ) (a : Seq) (b : ℕ → Seq)
    (ha : ∀ n, 0≤a n) (α : ℝ) (hα : 0<α)
    (hb : ∀ i<m, ∀ n, α≤b i n) (k : ℕ) (hk : k≤m) :
    Function.Bijective (shiftedFirstOrderComposition m a b k) ↔
      ∀ i<k, ∃ C ρ : ℝ, 1≤C ∧ 0<ρ ∧ ρ<1 ∧
        ∀ s N, blockProduct (fun n => a (n+m+1)/b i (n+(m-i))) s N ≤ C*ρ^N := by
  induction k with
  | zero => simp [shiftedFirstOrderComposition, Function.bijective_id]
  | succ k ih =>
    have hkm : k<m := by omega
    have hsingle := firstOrderMap_bijective_iff_geometric (translate (m+1) a)
      (translate (m-k) (b k)) (fun n => ha _) α hα (fun n => hb k hkm _)
    have hi := ih (by omega)
    have hinj : Function.Injective (shiftedFirstOrder m k a b) :=
      firstOrderMap_injective _ _ (fun n => ne_of_gt (lt_of_lt_of_le hα (hb k hkm _)))
    have hcomp : Function.Bijective (shiftedFirstOrderComposition m a b (k+1)) ↔
        Function.Bijective (shiftedFirstOrderComposition m a b k) ∧
        Function.Bijective (shiftedFirstOrder m k a b) := by
      constructor
      · intro hc
        change Function.Bijective (fun x => shiftedFirstOrder m k a b (shiftedFirstOrderComposition m a b k x)) at hc
        have hs : Function.Surjective (shiftedFirstOrder m k a b) := hc.2.of_comp
        refine ⟨⟨hc.1.of_comp,?_⟩,hinj,hs⟩
        intro y
        obtain ⟨x,hx⟩ := hc.2 (shiftedFirstOrder m k a b y)
        exact ⟨x,hinj hx⟩
      · rintro ⟨hprev,hlast⟩
        exact hlast.comp hprev
    rw [hcomp, hi]
    change (_ ∧ Function.Bijective (firstOrderMap _ _)) ↔ _
    rw [hsingle]
    simp only [translate_apply, Nat.add_assoc]
    constructor
    · rintro ⟨hprev,hlast⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | rfl
      · exact hprev i h
      · exact hlast
    · intro h
      exact ⟨fun i hi => h i (by omega),h k (by omega)⟩

#print axioms shiftedFirstOrderComposition_apply
#print axioms shiftedFirstOrderComposition_bijective_iff

/-- The remainder matrix is the actual ordered product of its `m`
bidiagonal factors. -/
def finiteProductBand (m : ℕ) (b : ℕ → Seq) : LowerBand m :=
  lowerProductBand (fun i : Fin m => b i.val)

theorem bandCoefficient_finiteProduct (m : ℕ) (b : ℕ → Seq) (s j : ℕ) :
    bandCoefficient (finiteProductBand m b) s j =
      productCoefficients (fun i n => b i n) m s (j+s) := by
  cases s with
  | zero => simp
  | succ s =>
    by_cases hs : s<m
    · rw [bandCoefficient_coordinate _ ⟨s,hs⟩]
      exact productCoefficient_eq_productCoefficients b m (s+1) j
    · rw [bandCoefficient_outside _ _ (by omega)]
      simp [productCoefficients_band _ m (s+1) _ (by omega)]

/-- The Banach-space elimination agrees, coefficient by coefficient,
with the exact row equations of the banded matrix derivative. -/
theorem residualMap_product_raw (m : ℕ) (a : Seq) (b : ℕ → Seq) (h : Seq) (s j : ℕ) :
    residualMap a (finiteProductBand m b) s h j =
      eliminate a (leftVariation (initialExtension (m+1) h)
        (productCoefficients (fun i n => b i n) m)) s (j+s) := by
  induction s with
  | zero => rfl
  | succ s ih =>
    rw [residualMap_succ, bandCoefficient_finiteProduct, ih]
    simp only [eliminate, leftVariation]
    rw [show j+(s+1)-1=j+s by omega, show j+(s+1)=j+s+1 by omega]

/-- The scalar residual of the actual matrix derivative equals the
composition of the first-order operators on bounded sequences. -/
theorem residualMap_product_eq_composition (m : ℕ) (a : Seq) (b : ℕ → Seq) :
    residualMap a (finiteProductBand m b) (m+1) =
      shiftedFirstOrderComposition m a b m := by
  apply ContinuousLinearMap.ext
  intro h
  apply BoundedContinuousFunction.ext
  intro j
  rw [residualMap_product_raw, shiftedFirstOrderComposition_apply _ _ _ _ _ (le_refl _) j]
  change scalarResidual a (initialExtension (m+1) h)
      (productCoefficients (fun i n => b i n) m) m (j+(m+1)) = _
  rw [scalarResidual_eq_firstOrderProduct, Nat.add_assoc]

/-- Arbitrary-bandwidth extraction criterion: the actual derivative of
L(a) L(b₀)⋯L(b_{m-1}), with the first m entries of a fixed, is bijective
exactly under the uniform geometric conditions for all scalar factors. -/
theorem lower_extraction_bijective_iff (m : ℕ) (a : Seq) (b : ℕ → Seq)
    (ha : ∀ n, 0≤a n) (α : ℝ) (hα : 0<α) (hb : ∀ i<m, ∀ n, α≤b i n) :
    Function.Bijective (fixedExtractionDerivative a (finiteProductBand m b)) ↔
      ∀ i<m, ∃ C ρ : ℝ, 1≤C ∧ 0<ρ ∧ ρ<1 ∧
        ∀ s N, blockProduct (fun n => a (n+m+1)/b i (n+(m-i))) s N ≤ C*ρ^N := by
  rw [fixedExtraction_bijective_iff, residualMap_product_eq_composition]
  exact shiftedFirstOrderComposition_bijective_iff m a b ha α hα hb m (le_refl _)

#print axioms residualMap_product_eq_composition
#print axioms lower_extraction_bijective_iff

/-- Uniqueness in the scalar recurrence gives uniqueness of the entire
matrix derivative, without a geometric hypothesis. -/
theorem fixedExtraction_injective_of_residual {m : ℕ} (a : Seq) (G : LowerBand m)
    (hinj : Function.Injective (residualMap a G (m+1))) :
    Function.Injective (fixedExtractionDerivative a G) := by
  intro x y he
  rcases x with ⟨h,R⟩
  rcases y with ⟨k,S⟩
  have ht := congrArg (eliminationMap a (m+1) (m+1)) he
  rw [elimination_fixedExtraction _ _ _ _ _ (le_refl _),
    elimination_fixedExtraction _ _ _ _ _ (le_refl _),
    strictCoefficientMap_outside m (m+1) (by omega)] at ht
  have hh : h=k := hinj (by simpa using ht)
  subst k
  have hRS : R=S := by
    funext r
    have ht := congrArg (eliminationMap a (m+1) (r.val+1)) he
    rw [elimination_fixedExtraction _ _ _ _ _ (by omega),
      elimination_fixedExtraction _ _ _ _ _ (by omega)] at ht
    simpa only [strictCoefficientMap_coordinate] using add_left_cancel ht
  subst S
  rfl

theorem shiftedFirstOrderComposition_injective (m : ℕ) (a : Seq) (b : ℕ → Seq)
    (hb : ∀ i<m, ∀ n, b i n ≠ 0) (k : ℕ) (hk : k≤m) :
    Function.Injective (shiftedFirstOrderComposition m a b k) := by
  induction k with
  | zero => exact Function.injective_id
  | succ k ih =>
    have hfirst : Function.Injective (shiftedFirstOrder m k a b) :=
      firstOrderMap_injective _ _ (fun n => hb k (by omega) _)
    exact hfirst.comp (ih (by omega))

/-- The fixed-initial-entry extraction derivative is always injective
when the remaining positive factors have nonzero entries. -/
theorem lower_extraction_injective (m : ℕ) (a : Seq) (b : ℕ → Seq)
    (hb : ∀ i<m, ∀ n, b i n ≠ 0) :
    Function.Injective (fixedExtractionDerivative a (finiteProductBand m b)) := by
  apply fixedExtraction_injective_of_residual
  rw [residualMap_product_eq_composition]
  exact shiftedFirstOrderComposition_injective m a b hb m (le_refl _)

#print axioms lower_extraction_injective

#print axioms firstOrderMap_normalization
#print axioms firstOrderMap_injective
#print axioms firstOrderMap_bijective_iff_geometric
#print axioms composition_bijective_iff

end BTP.GeneralStability
