import FullFixedCriterion
import FullFixedDerivative
import LDUInjectivity

noncomputable section
open Finset Filter
open scoped Topology BigOperators
namespace BTP.GeneralStability
open BTP BTP.SemiInfinite BTP.Stability BTP.Stability.BandLDU

/-- The joint inverse row sums for the actual two triangular products. -/
def JointInverseRowsBounded {p q : ℕ} (a : Fin p → Seq) (b : Fin q → Seq) : Prop :=
  ∃ Z : ℝ, ∀ n, ∑ s ∈ range (n+1),
    inverseEntries (reversedEntries a) p n s*inverseEntries (reversedEntries b) q n s≤Z

theorem factorBase_analytic_iff_joint_rows (p q : ℕ)
    (a : Fin (p+1) → Seq) (d : Seq) (b : Fin (q+1) → Seq)
    {α M : ℝ} (hα : 0<α) (hM : 0≤M)
    (ha : ∀ i n, α≤a i n) (hb : ∀ j n, α≤b j n) (hd : ∀ n, α≤d n)
    (haM : ∀ i n, |a i n|≤M) (hbM : ∀ j n, |b j n|≤M) :
    AnalyticLDUSection (factorBase a d b) ↔ JointInverseRowsBounded a b := by
  have har : ∀ i<p+1, ∀ n, 0<n → min α 1≤reversedEntries a i n :=
    fun i hi n _ => reversedEntries_lower a (min_le_left _ _) ha i hi n
  have hbr : ∀ i<q+1, ∀ n, 0<n → min α 1≤reversedEntries b i n :=
    fun i hi n _ => reversedEntries_lower b (min_le_left _ _) hb i hi n
  have harM : ∀ i<p+1, ∀ n, 0<n → |reversedEntries a i n|≤M :=
    fun i hi n _ => reversedEntries_upper a haM i hi n
  have hbrM : ∀ i<q+1, ∀ n, 0<n → |reversedEntries b i n|≤M :=
    fun i hi n _ => reversedEntries_upper b hbM i hi n
  have hdne : ∀ n,d n≠0 := fun n => ne_of_gt (lt_of_lt_of_le hα (hd n))
  have hdinv : ∀ n, |(d n)⁻¹|≤1/α := by
    intro n
    rw [abs_of_pos (inv_pos.mpr (lt_of_lt_of_le hα (hd n))),one_div]
    exact inv_anti₀ hα (hd n)
  have he := actual_ldu_analytic_iff_row_bound (reversedEntries a) (reversedEntries b)
    p q d hdne (lt_min hα zero_lt_one) (min_le_right _ _) hM (by positivity)
    har hbr harM hbrM hdinv
  rw [reversed_factor_base] at he
  exact he

theorem joint_rows_imply_cross (p q : ℕ)
    (a : Fin (p+1) → Seq) (b : Fin (q+1) → Seq)
    {α : ℝ} (hα : 0<α) (ha : ∀ i n,α≤a i n) (hb : ∀ j n,α≤b j n)
    (hrows : JointInverseRowsBounded a b) :
    GeometricDecay (fun n => a (Fin.last p) n*b (Fin.last q) n) := by
  obtain ⟨Z,hZ⟩ := hrows
  have har : ∀ i<p+1,∀ n,0<n → 0≤reversedEntries a i n :=
    fun i hi n _ => (reversedEntries_positive a hα ha i hi n).le
  have hbr : ∀ i<q+1,∀ n,0<n → 0≤reversedEntries b i n :=
    fun i hi n _ => (reversedEntries_positive b hα hb i hi n).le
  have he := cross_decay_of_inverse_row_bound
    (reversedEntries a 0) (reversedEntries b 0)
    (inverseEntries (reversedEntries a) (p+1))
    (inverseEntries (reversedEntries b) (q+1))
    (fun n => (reversedEntries_positive a hα ha 0 (by omega) n).le)
    (fun n => (reversedEntries_positive b hα hb 0 (by omega) n).le)
    (fun n s hsn => by
      have hh := actual_inverse_last_lower (reversedEntries a) p har s (n-s)
      simpa only [Nat.add_sub_of_le hsn] using hh)
    (fun n s hsn => by
      have hh := actual_inverse_last_lower (reversedEntries b) q hbr s (n-s)
      simpa only [Nat.add_sub_of_le hsn] using hh) hZ
  simpa only [GeometricDecay,reversedEntries_zero] using he

/-- The full local section forces surjectivity of the triangular
multiplication derivative; formal LDU uniqueness is the only cancellation
used in this step. -/
theorem full_fixed_implies_triangular_surjective {p q : ℕ}
    (a : Fin p → Seq) (d : Seq) (b : Fin q → Seq)
    (hd : ∀ n,d n≠0) {M : ℝ} (hM : 0≤M)
    (haM : ∀ i n,|a i n|≤M) (hbM : ∀ j n,|b j n|≤M)
    (hchoice : FullFixedPositiveAnalyticChoice a d b) :
    Function.Surjective (fixedTriangularDerivative a b) := by
  obtain ⟨R,hR⟩ := full_fixed_choice_derivative_rightInverse a d b hchoice
  have hinj := factorBase_derivative_injective a d b hd hM haM hbM
  intro v
  refine ⟨R (lduProductDerivative (factorBase a d b) v),?_⟩
  apply hinj
  exact congrArg (fun A : FullBand p q →L[ℝ] FullBand p q =>
    A (lduProductDerivative (factorBase a d b) v)) hR

/-- Necessity of both adjacent conditions in arbitrary full bandwidth. -/
theorem full_fixed_implies_adjacent {p q : ℕ}
    (a : Fin p → Seq) (d : Seq) (b : Fin q → Seq)
    {α M : ℝ} (hα : 0<α) (hM : 0≤M)
    (ha : ∀ i n,α≤a i n) (hb : ∀ j n,α≤b j n) (hd : ∀ n,α≤d n)
    (haM : ∀ i n,|a i n|≤M) (hbM : ∀ j n,|b j n|≤M)
    (hchoice : FullFixedPositiveAnalyticChoice a d b) :
    ManuscriptAdjacentGeometric p a ∧ ManuscriptAdjacentGeometric q b := by
  have hsurj := full_fixed_implies_triangular_surjective a d b
    (fun n => ne_of_gt (lt_of_lt_of_le hα (hd n))) hM haM hbM hchoice
  have hLa : Function.Surjective (fixedProductDerivative p a) := by
    intro E
    obtain ⟨v,hv⟩ := hsurj (E,0,0)
    exact ⟨v.1,congrArg Prod.fst hv⟩
  have hUb : Function.Surjective (fixedProductDerivative q b) := by
    intro E
    obtain ⟨v,hv⟩ := hsurj (0,0,E)
    exact ⟨v.2.2,congrArg (fun x : FullBand p q => x.2.2) hv⟩
  exact ⟨(fixedProductDerivative_bijective_iff_manuscript p a α hα ha).mp
    ⟨fixedProductDerivative_injective p a (fun i n => ne_of_gt (lt_of_lt_of_le hα (ha i n))),hLa⟩,
    (fixedProductDerivative_bijective_iff_manuscript q b α hα hb).mp
    ⟨fixedProductDerivative_injective q b (fun i n => ne_of_gt (lt_of_lt_of_le hα (hb i n))),hUb⟩⟩

/-- Complete fixed-data full-band theorem. All conditions concern the
specified bounded positive bidiagonal factors; no inverses or local
factorization maps are included among the hypotheses. -/
theorem full_fixed_positive_factorization_iff (p q : ℕ)
    (a : Fin (p+1) → Seq) (d : Seq) (b : Fin (q+1) → Seq)
    {α M : ℝ} (hα : 0<α) (hM : 0≤M)
    (ha : ∀ i n,α≤a i n) (hb : ∀ j n,α≤b j n) (hd : ∀ n,α≤d n)
    (haM : ∀ i n,|a i n|≤M) (hbM : ∀ j n,|b j n|≤M) :
    FullFixedPositiveAnalyticChoice a d b ↔
      ManuscriptAdjacentGeometric (p+1) a ∧ ManuscriptAdjacentGeometric (q+1) b ∧
      GeometricDecay (fun n => a (Fin.last p) n*b (Fin.last q) n) := by
  constructor
  · intro hchoice
    have hadj := full_fixed_implies_adjacent a d b hα hM ha hb hd haM hbM hchoice
    have hrows := (factorBase_analytic_iff_joint_rows p q a d b hα hM ha hb hd haM hbM).mp
      (full_fixed_choice_implies_analytic_ldu a d b hchoice)
    exact ⟨hadj.1,hadj.2,joint_rows_imply_cross p q a b hα ha hb hrows⟩
  · rintro ⟨hga,hgb,hcross⟩
    exact full_fixed_positive_of_geometric p q a d b hα hM ha hb hd haM hbM hga hgb hcross

#print axioms full_fixed_positive_factorization_iff
end BTP.GeneralStability
