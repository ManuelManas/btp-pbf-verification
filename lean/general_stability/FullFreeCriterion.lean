import FullFixedEquivalence
import FullFreeTransfer
import FullDerivativeSplit

/-! The complete full-band criterion with variable initial entries:
pairwise exponential dichotomies on both triangular sides, together
with the joint row bound for the actual signed triangular inverses. -/
noncomputable section
open Filter
open scoped Topology
namespace BTP.GeneralStability
open BTP.Stability.BandLDU

/-- Necessity of every pair condition, including non-adjacent pairs. -/
theorem full_free_implies_pairs {p q : ℕ}
    (a : Fin p → Seq) (d : Seq) (b : Fin q → Seq)
    {α M : ℝ} (hα : 0<α) (hM : 0≤M)
    (ha : ∀ i n,α≤a i n) (hb : ∀ j n,α≤b j n) (hd : ∀ n,α≤d n)
    (haM : ∀ i n,|a i n|≤M) (hbM : ∀ j n,|b j n|≤M)
    (hchoice : FullFreePositiveAnalyticChoice a d b) :
    FreePairCondition p a ∧ FreePairCondition q b := by
  obtain ⟨R,hR⟩ := full_free_choice_derivative_rightInverse a d b hchoice
  have hinj := factorBase_derivative_injective a d b
    (fun n => ne_of_gt (lt_of_lt_of_le hα (hd n))) hM haM hbM
  obtain ⟨hL,hU⟩ := block_derivative_right_inverses
    (lduProductDerivative (factorBase a d b)) (freeTriangularDerivative a b) R
    (freeProductDerivative p a) (freeProductDerivative q b)
    (fun _ => rfl) hinj hR
  exact ⟨(freeProductDerivative_rightInverse_iff_pairs p a α hα ha).mp hL,
    (freeProductDerivative_rightInverse_iff_pairs q b α hα hb).mp hU⟩

/-- Full variable-data positive factorization in arbitrary positive
lower and upper bandwidths. The right-hand side contains only explicit
scalar conditions on the prescribed factors and their true inverses. -/
theorem full_free_positive_factorization_iff (p q : ℕ)
    (a : Fin (p+1) → Seq) (d : Seq) (b : Fin (q+1) → Seq)
    {α M : ℝ} (hα : 0<α) (hM : 0≤M)
    (ha : ∀ i n,α≤a i n) (hb : ∀ j n,α≤b j n) (hd : ∀ n,α≤d n)
    (haM : ∀ i n,|a i n|≤M) (hbM : ∀ j n,|b j n|≤M) :
    FullFreePositiveAnalyticChoice a d b ↔
      FreePairCondition (p+1) a ∧ FreePairCondition (q+1) b ∧
      JointInverseRowsBounded a b := by
  constructor
  · intro hchoice
    have hpairs := full_free_implies_pairs a d b hα hM ha hb hd haM hbM hchoice
    have hrows := (factorBase_analytic_iff_joint_rows p q a d b hα hM ha hb hd haM hbM).mp
      (full_free_choice_implies_analytic_ldu a d b hchoice)
    exact ⟨hpairs.1,hpairs.2,hrows⟩
  · rintro ⟨hpa,hpb,hrows⟩
    exact full_free_positive_of_ldu_and_pairs a d b hα ha hd hb hpa hpb
      ((factorBase_analytic_iff_joint_rows p q a d b hα hM ha hb hd haM hbM).mpr hrows)

/-- The identical criterion expressed with the manuscript's row-indexed
pair quotients, rather than the reindexed extraction sequences. -/
theorem full_free_positive_factorization_iff_manuscript (p q : ℕ)
    (a : Fin (p+1) → Seq) (d : Seq) (b : Fin (q+1) → Seq)
    {α M : ℝ} (hα : 0<α) (hM : 0≤M)
    (ha : ∀ i n,α≤a i n) (hb : ∀ j n,α≤b j n) (hd : ∀ n,α≤d n)
    (haM : ∀ i n,|a i n|≤M) (hbM : ∀ j n,|b j n|≤M) :
    FullFreePositiveAnalyticChoice a d b ↔
      ManuscriptFreePairCondition (p+1) a ∧ ManuscriptFreePairCondition (q+1) b ∧
      JointInverseRowsBounded a b := by
  rw [full_free_positive_factorization_iff p q a d b hα hM ha hb hd haM hbM,
    freePairCondition_iff_manuscript,freePairCondition_iff_manuscript]

/-- Both kinds of positive analytic factor choice are locally Lipschitz
in the uniform factor norm, not merely in their initial coordinates. -/
theorem full_fixed_choice_locally_lipschitz {p q : ℕ}
    (a : Fin p → Seq) (d : Seq) (b : Fin q → Seq)
    (h : FullFixedPositiveAnalyticChoice a d b) :
    ∃ g : FullBand p q → FullBand p q,
      AnalyticAt ℝ g (lduProduct (factorBase a d b)) ∧
      g (lduProduct (factorBase a d b))=0 ∧
      (∀ᶠ T in 𝓝 (lduProduct (factorBase a d b)),fixedFullProduct a d b (g T)=T) ∧
      ∃ K,∃ s ∈ 𝓝 (lduProduct (factorBase a d b)),LipschitzOnWith K g s := by
  obtain ⟨g,hg,hg0,hprod⟩ := h
  exact ⟨g,hg,hg0,hprod.mono (fun _ h => h.1),
    hg.hasStrictFDerivAt.exists_lipschitzOnWith⟩

theorem full_free_choice_locally_lipschitz {p q : ℕ}
    (a : Fin p → Seq) (d : Seq) (b : Fin q → Seq)
    (h : FullFreePositiveAnalyticChoice a d b) :
    ∃ g : FullBand p q → FullBand p q,
      AnalyticAt ℝ g (lduProduct (factorBase a d b)) ∧
      g (lduProduct (factorBase a d b))=0 ∧
      (∀ᶠ T in 𝓝 (lduProduct (factorBase a d b)),freeFullProduct a d b (g T)=T) ∧
      ∃ K,∃ s ∈ 𝓝 (lduProduct (factorBase a d b)),LipschitzOnWith K g s := by
  obtain ⟨g,hg,hg0,hprod⟩ := h
  exact ⟨g,hg,hg0,hprod.mono (fun _ h => h.1),
    hg.hasStrictFDerivAt.exists_lipschitzOnWith⟩

#print axioms full_free_positive_factorization_iff
#print axioms full_free_positive_factorization_iff_manuscript
#print axioms full_fixed_choice_locally_lipschitz
#print axioms full_free_choice_locally_lipschitz
end BTP.GeneralStability
