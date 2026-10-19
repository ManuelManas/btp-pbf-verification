import QuotientBandOperator
import FreeExtractionInverse
import LowerGeneralCriterion

set_option maxHeartbeats 2000000
noncomputable section
namespace BTP.GeneralStability
open BTP.Stability BTP.FreeScalar

/-- Every pair of factor sequences, with the row shift forced by its
position in the ordered product, must have a uniform scalar dichotomy. -/
def FreePairCondition (p : ℕ) (a : Fin p → Seq) : Prop :=
  ∀ i j : Fin p,i<j →
    Geometric (fun n => a i (n+(j.val-i.val))/a j n) ∨
    Geometric (fun n => (a i (n+(j.val-i.val))/a j n)⁻¹)

def freeExtractionHeadTail {m : ℕ} (a : Seq) (G : LowerBand m) :
    LowerBand (m+1) →L[ℝ] LowerBand (m+1) :=
  (freeExtractionDerivative a G).comp
    ((ContinuousLinearMap.proj 0).prod (tailCLM m))

theorem freeExtractionHeadTail_preserves {m : ℕ} (a : Seq) (G : LowerBand m) :
    PreservesBandCZero (freeExtractionHeadTail a G) := by
  intro E hE
  exact freeExtractionDerivative_preserves_cZero a G (E 0) (Fin.tail E)
    (hE 0) (fun r => hE r.succ)

def quotientFreeExtraction {m : ℕ} (a : Seq) (G : LowerBand m) :
    (Fin (m+1) → SequenceQuotient) →ₗ[ℝ] (Fin (m+1) → SequenceQuotient) :=
  quotientBandOperator (freeExtractionHeadTail a G) (freeExtractionHeadTail_preserves a G)

theorem quotientFreeComposition_bijective_of_pairs (a : Seq) (b : ℕ → Seq)
    (α : ℝ) (hα : 0<α) (ha : ∀ n,α≤a n) (m : ℕ)
    (hb : ∀ i<m,∀ n,α≤b i n)
    (hg : ∀ i<m,Geometric (fun n => a (n+i+1)/b i n) ∨
      Geometric (fun n => (a (n+i+1)/b i n)⁻¹)) :
    Function.Bijective (quotientFreeComposition a b m) := by
  induction m with
  | zero => exact Function.bijective_id
  | succ m ih =>
    exact (quotientFreeFirstOrder_bijective_of_dichotomy m a b α hα ha
      (hb m (by omega)) (hg m (by omega))).comp
      (ih (fun i hi n => hb i (by omega) n) (fun i hi => hg i (by omega)))

/-- Null classes of the complete extraction derivative are controlled by
its scalar quotient equation and the finite remainder formulas. -/
theorem quotientFreeExtraction_injective_of_pairs (m : ℕ) (a : Seq) (b : ℕ → Seq)
    (α : ℝ) (hα : 0<α) (ha : ∀ n,α≤a n) (hb : ∀ i<m,∀ n,α≤b i n)
    (hg : ∀ i<m,Geometric (fun n => a (n+i+1)/b i n) ∨
      Geometric (fun n => (a (n+i+1)/b i n)⁻¹)) :
    Function.Injective (quotientFreeExtraction a (finiteProductBand m b)) := by
  apply (quotientBandOperator_injective_iff _ _).mpr
  intro E hE
  let G := finiteProductBand m b
  let F := freeExtractionDerivative a G (E 0,Fin.tail E)
  have hF : ∀ r,F r∈cZero := hE
  have ht := elimination_freeExtraction a G (E 0) (Fin.tail E) (m+1) (le_refl _)
  rw [strictCoefficientMap_outside m (m+1) (by omega)] at ht
  have hr : freeResidualMap a G (m+1) (E 0)∈cZero := by
    have hh := eliminationMap_preserves_cZero a F hF (m+1)
    change eliminationMap a (m+1) (m+1) (freeExtractionDerivative a G (E 0,Fin.tail E))∈cZero at hh
    rw [ht] at hh
    simpa using hh
  have hq := (quotientFreeComposition_bijective_of_pairs a b α hα ha m hb hg).1
  have he0 : E 0∈cZero := by
    have hc : quotientFreeComposition a b m (Submodule.Quotient.mk (E 0))=0 := by
      rw [quotientFreeComposition_actual,quotientOperator_mk,
        ←freeResidualMap_product_eq_composition]
      exact (Submodule.Quotient.eq cZero).mpr (by simpa using hr)
    have hz : (Submodule.Quotient.mk (E 0) : SequenceQuotient)=0 := by
      apply hq
      simpa only [map_zero] using hc
    simpa using (Submodule.Quotient.eq cZero).mp hz
  intro i
  refine Fin.cases he0 (fun r => ?_) i
  have ht := elimination_freeExtraction a G (E 0) (Fin.tail E) (r.val+1) (by omega)
  rw [strictCoefficientMap_coordinate] at ht
  have he : (Fin.tail E) r = eliminationMap a (m+1) (r.val+1) F -
      freeResidualMap a G (r.val+1) (E 0) := by
    change _ = eliminationMap a (m+1) (r.val+1)
      (freeExtractionDerivative a G (E 0,Fin.tail E)) - _
    rw [ht]
    abel
  rw [show E r.succ=(Fin.tail E) r by rfl,he]
  exact cZero.sub_mem (eliminationMap_preserves_cZero a F hF _)
    (freeResidualMap_preserves_cZero a G _ _ he0)

/-- Surjectivity in the componentwise quotient gives every first-factor
pair condition. This is the induction step for necessity in all widths. -/
theorem quotientFreeExtraction_surjective_implies_pairs (m : ℕ) (a : Seq) (b : ℕ → Seq)
    (α : ℝ) (hα : 0<α) (ha : ∀ n,α≤a n) (hb : ∀ i<m,∀ n,α≤b i n)
    (hs : Function.Surjective (quotientFreeExtraction a (finiteProductBand m b))) :
    ∀ i<m,Geometric (fun n => a (n+i+1)/b i n) ∨
      Geometric (fun n => (a (n+i+1)/b i n)⁻¹) := by
  apply (quotientFreeComposition_surjective_iff a b α hα ha m hb).mp
  intro y
  obtain ⟨f,rfl⟩ := Submodule.Quotient.mk_surjective cZero y
  obtain ⟨x,hx⟩ := hs (bandClass (m+1) (deepestBand m f))
  obtain ⟨x,rfl⟩ := bandClass_surjective (m+1) x
  change quotientBandOperator _ _ (bandClass (m+1) x)=_ at hx
  rw [quotientBandOperator_class] at hx
  let G := finiteProductBand m b
  let F := freeExtractionDerivative a G (x 0,Fin.tail x)
  have hd : ∀ r,(F-deepestBand m f) r∈cZero := by
    apply (bandClass_eq_zero_iff _).mp
    rw [map_sub]
    exact sub_eq_zero.mpr hx
  have he := eliminationMap_preserves_cZero a (F-deepestBand m f) hd (m+1)
  rw [map_sub,elimination_deepest] at he
  have ht := elimination_freeExtraction a G (x 0) (Fin.tail x) (m+1) (le_refl _)
  rw [strictCoefficientMap_outside m (m+1) (by omega)] at ht
  have hh : freeResidualMap a G (m+1) (x 0)-f∈cZero := by
    change eliminationMap a (m+1) (m+1) (freeExtractionDerivative a G (x 0,Fin.tail x))-f∈cZero at he
    rw [ht] at he
    simpa using he
  refine ⟨Submodule.Quotient.mk (x 0),?_⟩
  rw [quotientFreeComposition_actual,quotientOperator_mk,
    ←freeResidualMap_product_eq_composition]
  exact (Submodule.Quotient.eq cZero).mpr hh

/-- Recursive derivative on the genuine quotient of each sequence
coordinate. The next lemma proves its identification with the actual
matrix-product derivative, rather than assuming that relation. -/
def quotientFreeProductDerivative : (p : ℕ) → (Fin p → Seq) →
    (Fin p → SequenceQuotient) → (Fin p → SequenceQuotient)
  | 0,_ => fun _ => 0
  | p+1,a => fun h => quotientFreeExtraction (a 0) (lowerProductBand (Fin.tail a))
      (Fin.cons (h 0) (quotientFreeProductDerivative p (Fin.tail a) (Fin.tail h)))

theorem quotientFreeProductDerivative_actual (p : ℕ) (a h : Fin p → Seq) :
    quotientFreeProductDerivative p a (bandClass p h)=bandClass p (freeProductDerivative p a h) := by
  induction p with
  | zero => exact Subsingleton.elim _ _
  | succ p ih =>
    change quotientFreeExtraction (a 0) (lowerProductBand (Fin.tail a))
      (Fin.cons (bandClass (p+1) h 0)
        (quotientFreeProductDerivative p (Fin.tail a) (Fin.tail (bandClass (p+1) h)))) = _
    have he : Fin.tail (bandClass (p+1) h)=bandClass p (Fin.tail h) := rfl
    rw [he,ih]
    have hc : Fin.cons (bandClass (p+1) h 0)
        (bandClass p (freeProductDerivative p (Fin.tail a) (Fin.tail h))) =
        bandClass (p+1) (Fin.cons (h 0) (freeProductDerivative p (Fin.tail a) (Fin.tail h))) := by
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
    rw [hc]
    change quotientBandOperator _ _
      (bandClass (p+1) (Fin.cons (h 0) (freeProductDerivative p (Fin.tail a) (Fin.tail h)))) = _
    rw [quotientBandOperator_class,freeProductDerivative_succ_apply]
    rfl

theorem quotientFreeProductDerivative_surjective (p : ℕ) (a : Fin p → Seq)
    (hs : Function.Surjective (freeProductDerivative p a)) :
    Function.Surjective (quotientFreeProductDerivative p a) := by
  intro y
  obtain ⟨y,rfl⟩ := bandClass_surjective p y
  obtain ⟨x,hx⟩ := hs y
  exact ⟨bandClass p x,by rw [quotientFreeProductDerivative_actual,hx]⟩

/-- Pair conditions separate into those involving the first factor and
those belonging to the remaining ordered product. -/
theorem freePairCondition_succ_iff (p : ℕ) (a : Fin (p+1) → Seq) :
    FreePairCondition (p+1) a ↔
      (∀ j : Fin p,Geometric (fun n => a 0 (n+j.val+1)/a j.succ n) ∨
        Geometric (fun n => (a 0 (n+j.val+1)/a j.succ n)⁻¹)) ∧
      FreePairCondition p (Fin.tail a) := by
  constructor
  · intro h
    refine ⟨?_,?_⟩
    · intro j
      have hh := h 0 j.succ (by simp)
      simpa only [Fin.val_zero,Fin.val_succ,Nat.sub_zero,Nat.add_assoc] using hh
    · intro i j hij
      have hh := h i.succ j.succ (by simpa using hij)
      simpa only [Fin.val_succ,Nat.add_sub_add_right,Fin.tail] using hh
  · rintro ⟨hf,ht⟩ i j hij
    revert hij
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j
      · intro hh; exact False.elim (lt_irrefl _ hh)
      · intro _
        simpa only [Fin.val_zero,Fin.val_succ,Nat.sub_zero,Nat.add_assoc] using hf j
    · refine Fin.cases ?_ (fun j => ?_) j
      · intro hh; simp at hh
      · intro hh
        have hh' := ht i j (by simpa using hh)
        simpa only [Fin.val_succ,Nat.add_sub_add_right,Fin.tail] using hh'

/-- Necessity for the derivative of a product of any number of factors.
Only surjectivity in the quotient is needed at each induction step. -/
theorem quotientFreeProductDerivative_surjective_implies_pairs (p : ℕ) (a : Fin p → Seq)
    (α : ℝ) (hα : 0<α) (ha : ∀ i n,α≤a i n)
    (hs : Function.Surjective (quotientFreeProductDerivative p a)) :
    FreePairCondition p a := by
  induction p with
  | zero => intro i; exact Fin.elim0 i
  | succ p ih =>
    change Function.Surjective (fun h : Fin (p+1) → SequenceQuotient => quotientFreeExtraction (a 0)
      (lowerProductBand (Fin.tail a)) (Fin.cons (h 0)
        (quotientFreeProductDerivative p (Fin.tail a) (Fin.tail h)))) at hs
    have heS : Function.Surjective (quotientFreeExtraction (a 0) (lowerProductBand (Fin.tail a))) := hs.of_comp
    let b := extendFactors (Fin.tail a)
    have hb : ∀ i<p,∀ n,α≤b i n := by
      intro i hi n
      simpa [b,extendFactors,hi,Fin.tail] using ha (⟨i,hi⟩ : Fin p).succ n
    have heS' : Function.Surjective (quotientFreeExtraction (a 0) (finiteProductBand p b)) := by
      simpa [b] using heS
    have hfirst := quotientFreeExtraction_surjective_implies_pairs p (a 0) b α hα (ha 0) hb heS'
    have heI : Function.Injective (quotientFreeExtraction (a 0) (lowerProductBand (Fin.tail a))) := by
      simpa [b] using quotientFreeExtraction_injective_of_pairs p (a 0) b α hα (ha 0) hb hfirst
    have htail : Function.Surjective (quotientFreeProductDerivative p (Fin.tail a)) := by
      intro y
      obtain ⟨x,hx⟩ := hs (quotientFreeExtraction (a 0) (lowerProductBand (Fin.tail a)) (Fin.cons 0 y))
      have hh := congrArg Fin.tail (heI hx)
      exact ⟨Fin.tail x,by simpa using hh⟩
    apply (freePairCondition_succ_iff p a).mpr
    refine ⟨?_,ih (Fin.tail a) (fun i n => ha i.succ n) htail⟩
    intro j
    simpa [b,extendFactors,j.isLt,Fin.tail] using hfirst j.val j.isLt

/-- A local analytic choice would give a surjective derivative; this
criterion proves that every pair dichotomy is mathematically necessary. -/
theorem freeProductDerivative_surjective_implies_pairs (p : ℕ) (a : Fin p → Seq)
    (α : ℝ) (hα : 0<α) (ha : ∀ i n,α≤a i n)
    (hs : Function.Surjective (freeProductDerivative p a)) : FreePairCondition p a :=
  quotientFreeProductDerivative_surjective_implies_pairs p a α hα ha
    (quotientFreeProductDerivative_surjective p a hs)

#print axioms freeProductDerivative_surjective_implies_pairs

/-- A bounded right inverse for the full product derivative is assembled
from the explicit scalar inverses and finite remainder formulas. -/
theorem freeProductDerivative_rightInverse_of_pairs (p : ℕ) (a : Fin p → Seq)
    (α : ℝ) (hα : 0<α) (ha : ∀ i n,α≤a i n) (hg : FreePairCondition p a) :
    ∃ R : LowerBand p →L[ℝ] FactorVariations p,
      (freeProductDerivative p a).comp R=ContinuousLinearMap.id ℝ (LowerBand p) ∧
      PreservesBandCZero R := by
  induction p with
  | zero =>
    refine ⟨0,?_,?_⟩
    · apply ContinuousLinearMap.ext
      intro h
      exact Subsingleton.elim _ _
    · intro E _ i; exact Fin.elim0 i
  | succ p ih =>
    obtain ⟨hfirst,htail⟩ := (freePairCondition_succ_iff p a).mp hg
    obtain ⟨S,hS,hSc⟩ := ih (Fin.tail a) (fun i n => ha i.succ n) htail
    let b := extendFactors (Fin.tail a)
    have hb : ∀ i<p,∀ n,α≤b i n := by
      intro i hi n
      simpa [b,extendFactors,hi,Fin.tail] using ha (⟨i,hi⟩ : Fin p).succ n
    have hfirst' : ∀ i<p,Geometric (fun n => a 0 (n+i+1)/b i n) ∨
        Geometric (fun n => (a 0 (n+i+1)/b i n)⁻¹) := by
      intro i hi
      simpa [b,extendFactors,hi,Fin.tail] using hfirst ⟨i,hi⟩
    obtain ⟨V,hV,hVc⟩ := freeExtraction_rightInverse_of_pairs p (a 0) b α hα (ha 0) hb hfirst'
    have hV' : (freeExtractionDerivative (a 0) (lowerProductBand (Fin.tail a))).comp V=
        ContinuousLinearMap.id ℝ (LowerBand (p+1)) := by simpa [b] using hV
    let H := (ContinuousLinearMap.fst ℝ Seq (LowerBand p)).comp V
    let W := S.comp ((ContinuousLinearMap.snd ℝ Seq (LowerBand p)).comp V)
    let R : LowerBand (p+1) →L[ℝ] FactorVariations (p+1) :=
      ContinuousLinearMap.pi fun i => Fin.cases H (fun j => (ContinuousLinearMap.proj j).comp W) i
    have hhead (E : LowerBand (p+1)) : R E 0=(V E).1 := rfl
    have htailR (E : LowerBand (p+1)) : Fin.tail (R E)=S ((V E).2) := by
      funext j
      rfl
    refine ⟨R,?_,?_⟩
    · apply ContinuousLinearMap.ext
      intro E
      rw [ContinuousLinearMap.comp_apply,freeProductDerivative_succ_apply,hhead,htailR]
      have hh := congrArg (fun A : LowerBand p →L[ℝ] LowerBand p => A ((V E).2)) hS
      change freeProductDerivative p (Fin.tail a) (S ((V E).2))=(V E).2 at hh
      rw [hh]
      exact congrArg (fun A : LowerBand (p+1) →L[ℝ] LowerBand (p+1) => A E) hV'
    · intro E hE i
      have hv := hVc E hE
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hv.1
      · exact hSc ((V E).2) hv.2 j

/-- Complete arbitrary-bandwidth criterion for a bounded right inverse
of the derivative when the initial factor entries are allowed to vary. -/
theorem freeProductDerivative_rightInverse_iff_pairs (p : ℕ) (a : Fin p → Seq)
    (α : ℝ) (hα : 0<α) (ha : ∀ i n,α≤a i n) :
    (∃ R : LowerBand p →L[ℝ] FactorVariations p,
      (freeProductDerivative p a).comp R=ContinuousLinearMap.id ℝ (LowerBand p)) ↔
      FreePairCondition p a := by
  constructor
  · rintro ⟨R,hR⟩
    apply freeProductDerivative_surjective_implies_pairs p a α hα ha
    intro E
    exact ⟨R E,congrArg (fun A : LowerBand p →L[ℝ] LowerBand p => A E) hR⟩
  · intro hg
    obtain ⟨R,hR,_⟩ := freeProductDerivative_rightInverse_of_pairs p a α hα ha hg
    exact ⟨R,hR⟩

/-- Surjectivity alone is sufficient: positivity of the scalar weights
forces dichotomies, from which an explicit bounded right inverse follows. -/
theorem freeProductDerivative_surjective_iff_pairs (p : ℕ) (a : Fin p → Seq)
    (α : ℝ) (hα : 0<α) (ha : ∀ i n,α≤a i n) :
    Function.Surjective (freeProductDerivative p a) ↔ FreePairCondition p a := by
  constructor
  · exact freeProductDerivative_surjective_implies_pairs p a α hα ha
  · intro hg
    obtain ⟨R,hR,_⟩ := freeProductDerivative_rightInverse_of_pairs p a α hα ha hg
    intro E
    exact ⟨R E,congrArg (fun A : LowerBand p →L[ℝ] LowerBand p => A E) hR⟩

#print axioms freeProductDerivative_rightInverse_iff_pairs
#print axioms freeProductDerivative_surjective_iff_pairs

#print axioms quotientFreeExtraction_injective_of_pairs
#print axioms quotientFreeExtraction_surjective_implies_pairs
#print axioms quotientFreeProductDerivative_actual

end BTP.GeneralStability
