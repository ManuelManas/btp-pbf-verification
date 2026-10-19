import RelativeFullCriterion
import RelativeFullLocalInverse

/-! The main relative criterion including both local inverse identities.
The only hypotheses are positive raw factor entries and the explicit
geometric product conditions; the finite inverse data are constructed. -/
noncomputable section
open Filter
open scoped Topology
namespace BTP.RelativeStability
open BTP.GeneralStability

theorem relative_full_local_inverse_of_geometric {p q : ℕ}
    (a : Fin (p+1) → ℕ → ℝ) (d : ℕ → ℝ) (b : Fin (q+1) → ℕ → ℝ)
    (ha : ∀ i n,0<a i n) (hd : ∀ n,0<d n) (hb : ∀ i n,0<b i n)
    (hga : RelativeAdjacentGeometric a) (hgb : RelativeAdjacentGeometric b)
    (hcross : GeometricDecay (crossWeight (a ⟨p,by omega⟩) (b ⟨q,by omega⟩) d)) :
    ∃ g : FullBand (p+1) (q+1) → FullBand (p+1) (q+1),
      AnalyticAt ℝ g 0 ∧ g 0=0 ∧
      (∀ᶠ E in 𝓝 (0 : FullBand (p+1) (q+1)),relativeFullProduct a d b ha hd hb (g E)=E) ∧
      (∀ᶠ h in 𝓝 (0 : FullBand (p+1) (q+1)),g (relativeFullProduct a d b ha hd hb h)=h) ∧
      (∀ᶠ E in 𝓝 (0 : FullBand (p+1) (q+1)),
        (∀ i n,a i n/2≤relativePerturbedFactor a (g E).1 i n) ∧
        (∀ i n,b i n/2≤relativePerturbedFactor b (g E).2.2 i n) ∧
        (∀ n,d n/2≤d n*(1+(g E).2.1 n)) ∧
        (∀ i n,n<p+1-i.val → relativePerturbedFactor a (g E).1 i n=a i n) ∧
        (∀ i n,n<q+1-i.val → relativePerturbedFactor b (g E).2.2 i n=b i n)) ∧
      ∃ K,∃ s ∈ 𝓝 (0 : FullBand (p+1) (q+1)),LipschitzOnWith K g s :=
  relative_full_local_inverse a d b ha hd hb (factorRelativeData a d b hd)
    ((relative_full_positive_factorization_iff a d b ha hd hb).mpr ⟨hga,hgb,hcross⟩)

#print axioms relative_full_local_inverse_of_geometric
end BTP.RelativeStability
