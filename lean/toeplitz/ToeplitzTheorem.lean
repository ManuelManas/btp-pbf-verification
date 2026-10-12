import BandStructure
import NegativeRoots

/-!
# Theorem 3.2: dependency audit and formal consequences

The constructive implication and the implication PBF -> BTP are proved
without any additional mathematical hypothesis. The reverse implication
TN -> negative roots uses the polynomial consequence of Edrei's theorem.

IMPORTANT: `EdreiPolynomialInput` below is an explicit proposition, NOT a
proved theorem and NOT an axiom. The final characterization takes a proof
of that proposition as an argument. This file does not claim to provide a
Lean proof of Edrei's theorem, which is absent from the pinned mathlib.
-/

noncomputable section
namespace BTP.Toeplitz

/-- The classical external dependency, left visible in the final statement.
It is the finite-polynomial consequence of Edrei's classification, also
known as the finite Aissen--Schoenberg--Whitney root criterion. -/
def EdreiPolynomialInput : Prop :=
  ∀ P : Polynomial ℝ, 0 < P.coeff 0 → TN (symbolMatrix 0 P) → NegativeRoots P

/-- The new constructive part of Theorem 3.2, with no Edrei hypothesis. -/
theorem negative_roots_to_global_PBF (p q : ℕ) (P : Polynomial ℝ)
    (hdeg : P.natDegree = p+q) (hzero : 0 < P.coeff 0) (hroot : NegativeRoots P) :
    HasBoundedPBF p q (symbolOperator q P) ∧
      HasPBF p q (symbolOperator q P) ∧
      StrictBandTP p q (symbolMatrix q P) ∧ TN (symbolMatrix q P) := by
  have hb := negativeRoots_has_bounded_PBF p q P hdeg hzero hroot
  have hp := hb.hasPBF
  have ht := PBF_implies_BTP hp
  rw [symbolOperator_matrix] at ht
  exact ⟨hb, hp, ht.2, ht.1⟩

/-- All four manuscript conditions, and the bounded-factor strengthening.
The classical input is explicit: this is a conditional theorem until
`EdreiPolynomialInput` itself has a formal proof. -/
theorem theorem_3_2_given_Edrei (hEdrei : EdreiPolynomialInput)
    (p q : ℕ) (P : Polynomial ℝ) (hdeg : P.natDegree = p+q) (hzero : 0 < P.coeff 0) :
    (TN (symbolMatrix q P) ↔ StrictBandTP p q (symbolMatrix q P)) ∧
    (TN (symbolMatrix q P) ↔ NegativeRoots P) ∧
    (TN (symbolMatrix q P) ↔ HasPBF p q (symbolOperator q P)) ∧
    (TN (symbolMatrix q P) ↔ HasBoundedPBF p q (symbolOperator q P)) := by
  have htroot : TN (symbolMatrix q P) → NegativeRoots P :=
    fun ht => hEdrei P hzero ((symbolMatrix_TN_iff_shift_zero q P).mp ht)
  have hrt := negative_roots_to_global_PBF p q P hdeg hzero
  have hband := symbolMatrix_band p q P hdeg.le
  refine ⟨⟨fun ht => (hrt (htroot ht)).2.2.1, ?_⟩,
    ⟨htroot, fun hr => (hrt hr).2.2.2⟩,
    ⟨fun ht => (hrt (htroot ht)).2.1, ?_⟩,
    ⟨fun ht => (hrt (htroot ht)).1, ?_⟩⟩
  · exact fun ht => ((BandedTP_iff_strict hband).mpr ht).1
  · intro hp
    have ht : TN (opMatrix (symbolOperator q P)) := PBF_implies_TN hp
    rwa [symbolOperator_matrix] at ht
  · intro hb
    have ht : TN (opMatrix (symbolOperator q P)) := PBF_implies_TN hb.hasPBF
    rwa [symbolOperator_matrix] at ht

/-- The equivalence can use any formally established classical polynomial
root criterion with exactly the stated conclusion. There is no hidden
assumption about finite truncations or a pre-existing PBF. -/
theorem TN_to_global_PBF_given_Edrei (hEdrei : EdreiPolynomialInput)
    (p q : ℕ) (P : Polynomial ℝ) (hdeg : P.natDegree = p+q)
    (hzero : 0 < P.coeff 0) (hTN : TN (symbolMatrix q P)) :
    HasBoundedPBF p q (symbolOperator q P) :=
  (theorem_3_2_given_Edrei hEdrei p q P hdeg hzero).2.2.2.mp hTN

#print axioms negative_roots_to_global_PBF
#print theorem_3_2_given_Edrei
#print axioms theorem_3_2_given_Edrei
end BTP.Toeplitz
