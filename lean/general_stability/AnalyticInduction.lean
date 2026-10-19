import LowerStability
import AnalyticProductDerivative

noncomputable section
set_option maxHeartbeats 800000
namespace BTP.GeneralStability

theorem bijective_comp_iff_of_injective {X Y Z : Type*} (f : Y → Z) (g : X → Y)
    (hf : Function.Injective f) :
    Function.Bijective (fun x => f (g x)) ↔ Function.Bijective f ∧ Function.Bijective g := by
  constructor
  · rintro ⟨hi, hs⟩
    refine ⟨⟨hf, ?_⟩, ⟨?_, ?_⟩⟩
    · intro z
      obtain ⟨x,hx⟩ := hs z
      exact ⟨g x,hx⟩
    · intro x y hxy
      exact hi (congrArg f hxy)
    · intro y
      obtain ⟨x,hx⟩ := hs (f y)
      exact ⟨x,hf hx⟩
  · rintro ⟨hf',hg⟩
    exact hf'.comp hg

theorem headTailDerivative_bijective_iff {p : ℕ} (D : FactorVariations p → LowerBand p) :
    Function.Bijective (fun h : FactorVariations (p+1) => (h 0, D (Fin.tail h))) ↔
      Function.Bijective D := by
  constructor
  · rintro ⟨hi,hs⟩
    constructor
    · intro h k he
      have he' : (0, D h) = ((0 : Seq), D k) := by rw [he]
      have hh : Fin.cons (0 : Seq) h = Fin.cons 0 k := hi (by simpa using he')
      have ht := congrArg Fin.tail hh
      simpa using ht
    · intro R
      obtain ⟨h,hh⟩ := hs (0,R)
      exact ⟨Fin.tail h, congrArg Prod.snd hh⟩
  · rintro ⟨hi,hs⟩
    constructor
    · intro h k he
      have h0 := congrArg Prod.fst he
      have ht := hi (congrArg Prod.snd he)
      funext i
      refine Fin.cases h0 (fun j => congrFun ht j) i
    · rintro ⟨c,R⟩
      obtain ⟨h,hh⟩ := hs R
      refine ⟨Fin.cons c h, ?_⟩
      simpa using congrArg (fun v => (c,v)) hh

theorem fixedProductDerivative_succ_apply {p : ℕ} (a h : Fin (p+1) → Seq) :
    fixedProductDerivative (p+1) a h =
      fixedExtractionDerivative (a 0) (lowerProductBand (Fin.tail a))
        (h 0, fixedProductDerivative p (Fin.tail a) (Fin.tail h)) := rfl

/-- The algebraic injectivity of extraction makes the full derivative
bijective precisely when extraction and the remaining derivative are
both bijective. This is the induction step for arbitrary bandwidth. -/
theorem fixedProductDerivative_succ_bijective_iff {p : ℕ} (a : Fin (p+1) → Seq)
    (he : Function.Injective
      (fixedExtractionDerivative (a 0) (lowerProductBand (Fin.tail a)))) :
    Function.Bijective (fixedProductDerivative (p+1) a) ↔
      Function.Bijective (fixedExtractionDerivative (a 0) (lowerProductBand (Fin.tail a))) ∧
      Function.Bijective (fixedProductDerivative p (Fin.tail a)) := by
  have h := bijective_comp_iff_of_injective
    (fixedExtractionDerivative (a 0) (lowerProductBand (Fin.tail a)))
    (fun h : FactorVariations (p+1) => (h 0, fixedProductDerivative p (Fin.tail a) (Fin.tail h))) he
  rw [headTailDerivative_bijective_iff] at h
  exact h

theorem fixedProductDerivative_succ_injective {p : ℕ} (a : Fin (p+1) → Seq)
    (he : Function.Injective
      (fixedExtractionDerivative (a 0) (lowerProductBand (Fin.tail a))))
    (ht : Function.Injective (fixedProductDerivative p (Fin.tail a))) :
    Function.Injective (fixedProductDerivative (p+1) a) := by
  intro h k hh
  rw [fixedProductDerivative_succ_apply, fixedProductDerivative_succ_apply] at hh
  have hpair := he hh
  have h0 := congrArg Prod.fst hpair
  have htail := ht (congrArg Prod.snd hpair)
  funext i
  exact Fin.cases h0 (fun j => congrFun htail j) i

@[simp] theorem fixedProductDerivative_zero_bijective (a : Fin 0 → Seq) :
    Function.Bijective (fixedProductDerivative 0 a) := by
  constructor
  · intro x y _
    exact Subsingleton.elim _ _
  · intro x
    exact ⟨0, Subsingleton.elim _ _⟩

#print axioms fixedProductDerivative_succ_bijective_iff
#print axioms fixedProductDerivative_succ_injective

end BTP.GeneralStability
