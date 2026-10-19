import FreeQuotientExtraction
import FreeProductDerivative

noncomputable section
namespace BTP.GeneralStability
open BTP.FreeScalar

/-- Classes modulo c₀, taken in each actual subdiagonal or factor
sequence. -/
def bandClass (p : ℕ) : LowerBand p →ₗ[ℝ] (Fin p → SequenceQuotient) :=
  LinearMap.pi fun i => cZero.mkQ.comp (ContinuousLinearMap.proj (R := ℝ) i).toLinearMap

@[simp] theorem bandClass_apply {p : ℕ} (E : LowerBand p) (i : Fin p) :
    bandClass p E i = Submodule.Quotient.mk (E i) := rfl

theorem bandClass_surjective (p : ℕ) : Function.Surjective (bandClass p) := by
  intro y
  choose x hx using fun i : Fin p => Submodule.Quotient.mk_surjective cZero (y i)
  exact ⟨x,funext hx⟩

theorem bandClass_eq_zero_iff {p : ℕ} (E : LowerBand p) :
    bandClass p E=0 ↔ ∀ i,E i∈cZero := by
  constructor
  · intro h i
    have hi := congrFun h i
    change Submodule.Quotient.mk (E i)=Submodule.Quotient.mk (0 : Seq) at hi
    have hh := (Submodule.Quotient.eq cZero).mp hi
    simpa using hh
  · intro h
    funext i
    change Submodule.Quotient.mk (E i)=Submodule.Quotient.mk (0 : Seq)
    exact (Submodule.Quotient.eq cZero).mpr (by simpa using h i)

def PreservesBandCZero {p q : ℕ} (A : LowerBand p →L[ℝ] LowerBand q) : Prop :=
  ∀ E,(∀ i,E i∈cZero) → ∀ j,A E j∈cZero

/-- The induced operator is obtained by the universal property of the
actual kernel of the componentwise quotient map. -/
def quotientBandOperator {p q : ℕ} (A : LowerBand p →L[ℝ] LowerBand q)
    (hA : PreservesBandCZero A) : (Fin p → SequenceQuotient) →ₗ[ℝ] (Fin q → SequenceQuotient) :=
  ((bandClass p).ker.liftQ ((bandClass q).comp A.toLinearMap) (by
    intro E hE
    change bandClass q (A E)=0
    exact (bandClass_eq_zero_iff _).mpr (hA E ((bandClass_eq_zero_iff _).mp hE)))).comp
    ((bandClass p).quotKerEquivOfSurjective (bandClass_surjective p)).symm.toLinearMap

@[simp] theorem quotientBandOperator_class {p q : ℕ} (A : LowerBand p →L[ℝ] LowerBand q)
    (hA : PreservesBandCZero A) (E : LowerBand p) :
    quotientBandOperator A hA (bandClass p E)=bandClass q (A E) := by
  have he := LinearMap.quotKerEquivOfSurjective_apply_mk (bandClass p) (bandClass_surjective p) E
  rw [←he]
  simp only [quotientBandOperator,LinearMap.comp_apply,LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]
  rfl

theorem preservesBandCZero_comp {p q r : ℕ}
    (A : LowerBand q →L[ℝ] LowerBand r) (B : LowerBand p →L[ℝ] LowerBand q)
    (hA : PreservesBandCZero A) (hB : PreservesBandCZero B) :
    PreservesBandCZero (A.comp B) := fun E hE => hA _ (hB E hE)

theorem quotientBandOperator_comp {p q r : ℕ}
    (A : LowerBand q →L[ℝ] LowerBand r) (B : LowerBand p →L[ℝ] LowerBand q)
    (hA : PreservesBandCZero A) (hB : PreservesBandCZero B) :
    quotientBandOperator (A.comp B) (preservesBandCZero_comp A B hA hB) =
      (quotientBandOperator A hA).comp (quotientBandOperator B hB) := by
  apply LinearMap.ext
  intro E
  obtain ⟨E,rfl⟩ := bandClass_surjective p E
  simp only [LinearMap.comp_apply,quotientBandOperator_class,ContinuousLinearMap.comp_apply]

theorem quotientBandOperator_surjective {p q : ℕ}
    (A : LowerBand p →L[ℝ] LowerBand q) (hA : PreservesBandCZero A)
    (hs : Function.Surjective A) : Function.Surjective (quotientBandOperator A hA) := by
  intro y
  obtain ⟨y,rfl⟩ := bandClass_surjective q y
  obtain ⟨x,hx⟩ := hs y
  exact ⟨bandClass p x,by rw [quotientBandOperator_class,hx]⟩

/-- Injectivity of the induced map is precisely control of its null
classes: an output tending to zero in every coordinate forces the same
property of its input. -/
theorem quotientBandOperator_injective_iff {p q : ℕ}
    (A : LowerBand p →L[ℝ] LowerBand q) (hA : PreservesBandCZero A) :
    Function.Injective (quotientBandOperator A hA) ↔
      ∀ E,(∀ j,A E j∈cZero) → ∀ i,E i∈cZero := by
  constructor
  · intro hi E hE
    apply (bandClass_eq_zero_iff _).mp
    apply hi
    rw [quotientBandOperator_class,map_zero]
    exact (bandClass_eq_zero_iff _).mpr hE
  · intro hi x y hxy
    obtain ⟨x,rfl⟩ := bandClass_surjective p x
    obtain ⟨y,rfl⟩ := bandClass_surjective p y
    apply sub_eq_zero.mp
    rw [←map_sub]
    apply (bandClass_eq_zero_iff _).mpr
    apply hi
    apply (bandClass_eq_zero_iff _).mp
    rw [←quotientBandOperator_class A hA (x-y),map_sub,map_sub,hxy,sub_self]

#print axioms quotientBandOperator_class
#print axioms quotientBandOperator_comp
#print axioms quotientBandOperator_injective_iff

end BTP.GeneralStability
