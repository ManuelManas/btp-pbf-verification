import FreeExtraction
import FreeForward

noncomputable section
open Filter
open scoped Topology
namespace BTP.GeneralStability
open BTP.Stability
open BTP.FreeScalar

abbrev SequenceQuotient := Seq ⧸ cZero

def PreservesCZero (A : Seq →L[ℝ] Seq) : Prop :=
  ∀ v ∈ cZero, A v ∈ cZero

def quotientOperator (A : Seq →L[ℝ] Seq) (hA : PreservesCZero A) :
    SequenceQuotient →ₗ[ℝ] SequenceQuotient :=
  cZero.mapQ cZero A.toLinearMap hA

@[simp] theorem quotientOperator_mk (A : Seq →L[ℝ] Seq) (hA : PreservesCZero A) (v : Seq) :
    quotientOperator A hA (Submodule.Quotient.mk v) = Submodule.Quotient.mk (A v) := rfl

theorem preservesCZero_comp (A B : Seq →L[ℝ] Seq)
    (hA : PreservesCZero A) (hB : PreservesCZero B) : PreservesCZero (A.comp B) :=
  fun v hv => hA _ (hB v hv)

theorem quotientOperator_comp (A B : Seq →L[ℝ] Seq)
    (hA : PreservesCZero A) (hB : PreservesCZero B) :
    quotientOperator (A.comp B) (preservesCZero_comp A B hA hB) =
      (quotientOperator A hA).comp (quotientOperator B hB) := by
  apply LinearMap.ext
  intro v
  obtain ⟨v,rfl⟩ := Submodule.Quotient.mk_surjective cZero v
  rfl

theorem quotientOperator_surjective (A : Seq →L[ℝ] Seq) (hA : PreservesCZero A)
    (hs : Function.Surjective A) : Function.Surjective (quotientOperator A hA) := by
  intro v
  obtain ⟨v,rfl⟩ := Submodule.Quotient.mk_surjective cZero v
  obtain ⟨u,hu⟩ := hs v
  exact ⟨Submodule.Quotient.mk u,by rw [quotientOperator_mk,hu]⟩

theorem multiply_preserves_cZero (d : Seq) :
    PreservesCZero (ContinuousLinearMap.mul ℝ Seq d) := by
  intro v hv
  change Tendsto (fun n => d n*v n) atTop (𝓝 0)
  exact bdd_le_mul_tendsto_zero' ‖d‖
    (Eventually.of_forall (fun n => boundedSequence_abs_le d n)) hv

theorem translateMap_preserves_cZero (r : ℕ) : PreservesCZero (translate r) := by
  intro v hv
  change Tendsto (fun n => v (n+r)) atTop (𝓝 0)
  exact hv.comp (tendsto_add_atTop_nat r)

/-- A bounded pointwise reciprocal makes multiplication invertible also
on the genuine quotient by sequences tending to zero. -/
theorem quotient_multiply_bijective (d u : Seq) (hdu : ∀ n,d n*u n=1) :
    Function.Bijective (quotientOperator (ContinuousLinearMap.mul ℝ Seq d)
      (multiply_preserves_cZero d)) := by
  have hinv (v : Seq) : u*(d*v)=v := by
    apply BoundedContinuousFunction.ext
    intro n
    change u n*(d n*v n)=v n
    nlinarith only [congrArg (fun x : ℝ => x*v n) (hdu n)]
  have hinv' (v : Seq) : d*(u*v)=v := by
    apply BoundedContinuousFunction.ext
    intro n
    change d n*(u n*v n)=v n
    nlinarith only [congrArg (fun x : ℝ => x*v n) (hdu n)]
  constructor
  · intro x y he
    obtain ⟨x,rfl⟩ := Submodule.Quotient.mk_surjective cZero x
    obtain ⟨y,rfl⟩ := Submodule.Quotient.mk_surjective cZero y
    have hh := congrArg (quotientOperator (ContinuousLinearMap.mul ℝ Seq u)
      (multiply_preserves_cZero u)) he
    simpa only [quotientOperator_mk, ContinuousLinearMap.mul_apply',hinv] using hh
  · intro y
    obtain ⟨y,rfl⟩ := Submodule.Quotient.mk_surjective cZero y
    refine ⟨Submodule.Quotient.mk (u*y),?_⟩
    change Submodule.Quotient.mk (d*(u*y)) = _
    rw [hinv']

theorem freeFirstOrder_preserves_cZero (j : ℕ) (a : Seq) (b : ℕ → Seq) :
    PreservesCZero (freeFirstOrder j a b) := by
  intro v hv
  change Tendsto (fun n => freeFirstOrder j a b v n) atTop (𝓝 0)
  have hv' : Tendsto (fun n => v n) atTop (𝓝 0) := hv
  have hl := bdd_le_mul_tendsto_zero' ‖b j‖
    (Eventually.of_forall (fun n => boundedSequence_abs_le (b j) (n+1)))
    (hv'.comp (tendsto_add_atTop_nat 1))
  have hr := bdd_le_mul_tendsto_zero' ‖a‖
    (Eventually.of_forall (fun n => boundedSequence_abs_le a (n+j+2))) hv'
  simpa only [freeFirstOrder_apply,Function.comp_apply,sub_self] using hl.sub hr

def quotientFreeFirstOrder (j : ℕ) (a : Seq) (b : ℕ → Seq) :
    SequenceQuotient →ₗ[ℝ] SequenceQuotient :=
  quotientOperator (freeFirstOrder j a b) (freeFirstOrder_preserves_cZero j a b)

/-- The normalized quotient operator is an invertible diagonal
multiplication followed by the scalar quotient difference operator. -/
theorem quotientFreeFirstOrder_normalization (j : ℕ) (a : Seq) (b : ℕ → Seq)
    (α : ℝ) (hα : 0<α) (hb : ∀ n,α≤b j n) :
    quotientFreeFirstOrder j a b =
      (quotientOperator (ContinuousLinearMap.mul ℝ Seq (translate 1 (b j)))
        (multiply_preserves_cZero _)).comp
      (quotientDifference (translate (j+1) a * positiveReciprocal (b j) α hα hb)) := by
  apply LinearMap.ext
  intro v
  obtain ⟨v,rfl⟩ := Submodule.Quotient.mk_surjective cZero v
  change Submodule.Quotient.mk (freeFirstOrder j a b v) = _
  rw [freeFirstOrder_normalization j a b α hα hb]
  rfl

/-- Surjectivity of one scalar factor in the quotient forces the
corresponding pair dichotomy. -/
theorem quotientFreeFirstOrder_surjective_dichotomy (j : ℕ) (a : Seq) (b : ℕ → Seq)
    (ha : ∀ n,0<a n) (α : ℝ) (hα : 0<α) (hb : ∀ n,α≤b j n)
    (hs : Function.Surjective (quotientFreeFirstOrder j a b)) :
    Geometric (fun n => a (n+j+1)/b j n) ∨
      Geometric (fun n => (a (n+j+1)/b j n)⁻¹) := by
  let w := translate (j+1) a * positiveReciprocal (b j) α hα hb
  have hw : ∀ n,0<w n := by
    intro n
    change 0<a (n+(j+1))*(1/b j n)
    exact mul_pos (ha _) (one_div_pos.mpr (lt_of_lt_of_le hα (hb n)))
  have hd : Function.Bijective
      (quotientOperator (ContinuousLinearMap.mul ℝ Seq (translate 1 (b j)))
        (multiply_preserves_cZero _)) := by
    apply quotient_multiply_bijective _ (translate 1 (positiveReciprocal (b j) α hα hb))
    intro n
    change b j (n+1)*(1/b j (n+1))=1
    exact mul_one_div_cancel (ne_of_gt (lt_of_lt_of_le hα (hb _)))
  have hs' : Function.Surjective (quotientDifference w) := by
    intro y
    obtain ⟨x,hx⟩ := hs
      (quotientOperator (ContinuousLinearMap.mul ℝ Seq (translate 1 (b j)))
        (multiply_preserves_cZero _) y)
    rw [quotientFreeFirstOrder_normalization j a b α hα hb] at hx
    exact ⟨x,hd.1 hx⟩
  have hh := quotient_surjective_implies_dichotomy w hw hs'
  have he : (w : ℕ → ℝ) = fun n => a (n+j+1)/b j n := by
    funext n
    change a (n+(j+1))*(1/b j n)=_
    rw [Nat.add_assoc]
    ring
  simpa only [he] using hh

/-- Either direction of geometric decay makes a scalar extraction factor
invertible in the quotient. -/
theorem quotientFreeFirstOrder_bijective_of_dichotomy (j : ℕ) (a : Seq) (b : ℕ → Seq)
    (α : ℝ) (hα : 0<α) (ha : ∀ n,α≤a n) (hb : ∀ n,α≤b j n)
    (hg : Geometric (fun n => a (n+j+1)/b j n) ∨
      Geometric (fun n => (a (n+j+1)/b j n)⁻¹)) :
    Function.Bijective (quotientFreeFirstOrder j a b) := by
  let w := translate (j+1) a * positiveReciprocal (b j) α hα hb
  let u := b j * positiveReciprocal (translate (j+1) a) α hα (fun n => ha _)
  have hw : ∀ n,0<w n := by
    intro n
    change 0<a (n+(j+1))*(1/b j n)
    exact mul_pos (lt_of_lt_of_le hα (ha _)) (one_div_pos.mpr (lt_of_lt_of_le hα (hb n)))
  have hu : ∀ n,0<u n := by
    intro n
    change 0<b j n*(1/a (n+(j+1)))
    exact mul_pos (lt_of_lt_of_le hα (hb n)) (one_div_pos.mpr (lt_of_lt_of_le hα (ha _)))
  have huw : ∀ n,u n*w n=1 := by
    intro n
    change (b j n*(1/a (n+(j+1))))*(a (n+(j+1))*(1/b j n))=1
    have ha' : a (n+(j+1))≠0 := ne_of_gt (lt_of_lt_of_le hα (ha _))
    have hb' : b j n≠0 := ne_of_gt (lt_of_lt_of_le hα (hb n))
    field_simp
  have hew : (w : ℕ → ℝ) = fun n => a (n+j+1)/b j n := by
    funext n
    change a (n+(j+1))*(1/b j n)=_
    rw [Nat.add_assoc]
    ring
  have heu : (u : ℕ → ℝ) = fun n => (a (n+j+1)/b j n)⁻¹ := by
    funext n
    change b j n*(1/a (n+(j+1)))=_
    simp [div_eq_mul_inv,Nat.add_assoc]
  have hgu : Geometric w ∨ Geometric u := by
    simpa only [hew,heu] using hg
  have hq := quotientDifference_bijective_of_dichotomy w u hw hu huw hgu
  rw [quotientFreeFirstOrder_normalization j a b α hα hb]
  have hd : Function.Bijective
      (quotientOperator (ContinuousLinearMap.mul ℝ Seq (translate 1 (b j)))
        (multiply_preserves_cZero _)) := by
    apply quotient_multiply_bijective _ (translate 1 (positiveReciprocal (b j) α hα hb))
    intro n
    change b j (n+1)*(1/b j (n+1))=1
    exact mul_one_div_cancel (ne_of_gt (lt_of_lt_of_le hα (hb _)))
  exact hd.comp hq

def quotientFreeComposition (a : Seq) (b : ℕ → Seq) : ℕ → SequenceQuotient →ₗ[ℝ] SequenceQuotient
  | 0 => LinearMap.id
  | k+1 => (quotientFreeFirstOrder k a b).comp (quotientFreeComposition a b k)

theorem freeFirstOrderComposition_preserves_cZero (a : Seq) (b : ℕ → Seq) (k : ℕ) :
    PreservesCZero (freeFirstOrderComposition a b k) := by
  induction k with
  | zero => intro v hv; exact hv
  | succ k ih => exact preservesCZero_comp _ _ (freeFirstOrder_preserves_cZero k a b) ih

theorem quotientFreeComposition_actual (a : Seq) (b : ℕ → Seq) (k : ℕ) :
    quotientFreeComposition a b k =
      quotientOperator (freeFirstOrderComposition a b k)
        (freeFirstOrderComposition_preserves_cZero a b k) := by
  induction k with
  | zero =>
    apply LinearMap.ext
    intro v
    obtain ⟨v,rfl⟩ := Submodule.Quotient.mk_surjective cZero v
    rfl
  | succ k ih =>
    change (quotientFreeFirstOrder k a b).comp (quotientFreeComposition a b k) = _
    rw [ih]
    exact (quotientOperator_comp _ _ _ _).symm

/-- In the quotient, each leftmost surjective factor is invertible by the
scalar dichotomy. It can therefore be removed without commuting factors. -/
theorem quotientFreeComposition_surjective_iff (a : Seq) (b : ℕ → Seq)
    (α : ℝ) (hα : 0<α) (ha : ∀ n,α≤a n) (k : ℕ)
    (hb : ∀ i<k,∀ n,α≤b i n) :
    Function.Surjective (quotientFreeComposition a b k) ↔
      ∀ i<k, Geometric (fun n => a (n+i+1)/b i n) ∨
        Geometric (fun n => (a (n+i+1)/b i n)⁻¹) := by
  induction k with
  | zero => simp [quotientFreeComposition,Function.surjective_id]
  | succ k ih =>
    have hbk : ∀ n,α≤b k n := hb k (by omega)
    have hprev : ∀ i<k,∀ n,α≤b i n := fun i hi n => hb i (by omega) n
    constructor
    · intro hs
      change Function.Surjective (fun x => quotientFreeFirstOrder k a b (quotientFreeComposition a b k x)) at hs
      have hlast := quotientFreeFirstOrder_surjective_dichotomy k a b
        (fun n => lt_of_lt_of_le hα (ha n)) α hα hbk hs.of_comp
      have hlbij := quotientFreeFirstOrder_bijective_of_dichotomy k a b α hα ha hbk hlast
      have hrest : Function.Surjective (quotientFreeComposition a b k) := by
        intro y
        obtain ⟨x,hx⟩ := hs (quotientFreeFirstOrder k a b y)
        exact ⟨x,hlbij.1 hx⟩
      have hp := (ih hprev).mp hrest
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact hp i hi
      · exact hlast
    · intro hg
      have hlbij := quotientFreeFirstOrder_bijective_of_dichotomy k a b α hα ha hbk (hg k (by omega))
      have hp := (ih hprev).mpr (fun i hi => hg i (by omega))
      exact hlbij.2.comp hp

/-- Every pair between the extracted factor and a remaining factor must
have a uniform exponential dichotomy. The proof uses the actual matrix
derivative and the genuine quotient by c₀. -/
theorem freeExtraction_surjective_implies_pairs (m : ℕ) (a : Seq) (b : ℕ → Seq)
    (α : ℝ) (hα : 0<α) (ha : ∀ n,α≤a n) (hb : ∀ i<m,∀ n,α≤b i n)
    (hs : Function.Surjective (freeExtractionDerivative a (finiteProductBand m b))) :
    ∀ i<m, Geometric (fun n => a (n+i+1)/b i n) ∨
      Geometric (fun n => (a (n+i+1)/b i n)⁻¹) := by
  have hscalar := (freeExtraction_surjective_iff a (finiteProductBand m b)).mp hs
  rw [freeResidualMap_product_eq_composition] at hscalar
  have hquot := quotientOperator_surjective _ (freeFirstOrderComposition_preserves_cZero a b m) hscalar
  rw [←quotientFreeComposition_actual] at hquot
  exact (quotientFreeComposition_surjective_iff a b α hα ha m hb).mp hquot

#print axioms quotientFreeComposition_surjective_iff
#print axioms freeExtraction_surjective_implies_pairs

#print axioms quotientFreeFirstOrder_surjective_dichotomy

end BTP.GeneralStability
