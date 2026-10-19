import RelativeLDUSufficiency
import RelativeLDUNecessity

/-! The complete arbitrary-growth relative criterion in full bandwidth.
The assumptions refer only to the original positive factor entries and
geometric decay of their adjacent and crossed products. -/
noncomputable section
open Filter
open scoped Topology
namespace BTP.RelativeStability
open BTP BTP.GeneralStability BTP.Stability.BandLDU

/-- The actual finite sections and finite triangular inverses for the
unscaled factor lists. These data impose no boundedness assumptions. -/
def factorRelativeData {p q : ℕ} (a : Fin p → ℕ → ℝ)
    (d : ℕ → ℝ) (b : Fin q → ℕ → ℝ) (hd : ∀ n,0<d n) :
    RelativeLDUData (relativeFactorBase a) d (relativeFactorBase b) where
  s := actualData (rawReverse (extendRaw a) p) (rawReverse (extendRaw b) q) p q d
    (fun n=>ne_of_gt (hd n))
  lower_eq := fun N=>(rawUnitEntry_productBand_finite (extendRaw a) p N).symm
  upper_eq := by
    intro N
    ext i j
    exact (congrArg (fun M : Mat N=>M j i)
      (rawUnitEntry_productBand_finite (extendRaw b) q N)).symm
  diagonal_eq := rfl

/-- The differential of normalized LDU is injective even when the
original entries grow without bound. This follows from finite triangular
uniqueness; no analytic choice or inverse estimate is assumed. -/
theorem relative_factor_ldu_derivative_injective {p q : ℕ}
    (a : Fin p → ℕ → ℝ) (d : ℕ → ℝ) (b : Fin q → ℕ → ℝ)
    (ha : ∀ i n,0<a i n) (hd : ∀ n,0<d n) (hb : ∀ i n,0<b i n) :
    Function.Injective (relativeLDUProductDerivative (relativeFactorBase a) d (relativeFactorBase b)
      (relativeFactorBase_pos a ha) hd (relativeFactorBase_pos b hb) 0) :=
  (factorRelativeData a d b hd).derivative_injective
    (relativeFactorBase_pos a ha) hd (relativeFactorBase_pos b hb)

theorem relative_factor_ldu_analytic_of_geometric {p q : ℕ}
    (a : Fin (p+1) → ℕ → ℝ) (d : ℕ → ℝ) (b : Fin (q+1) → ℕ → ℝ)
    (ha : ∀ i n,0<a i n) (hd : ∀ n,0<d n) (hb : ∀ i n,0<b i n)
    (hga : RelativeAdjacentGeometric a) (hgb : RelativeAdjacentGeometric b)
    (hcross : GeometricDecay (crossWeight (a ⟨p,by omega⟩) (b ⟨q,by omega⟩) d)) :
    RelativeAnalyticLDUSection (relativeFactorBase a) d (relativeFactorBase b)
      (relativeFactorBase_pos a ha) hd (relativeFactorBase_pos b hb) := by
  apply relative_ldu_analytic_of_geometric_raw (extendRaw a) (extendRaw b) p q d
    (extendRaw_pos a ha) (extendRaw_pos b hb) hd
  · intro i hi
    simpa only [extendRaw,show i<p+1 by omega,hi,↓reduceDIte] using hga i hi
  · intro i hi
    simpa only [extendRaw,show i<q+1 by omega,hi,↓reduceDIte] using hgb i hi
  · have ea : extendRaw a p=a ⟨p,by omega⟩ := by funext n;simp [extendRaw]
    have eb : extendRaw b q=b ⟨q,by omega⟩ := by funext n;simp [extendRaw]
    rw [ea,eb]
    exact hcross

/-- Full-band relative positive analytic factorization with prescribed
initial entries is equivalent to geometric decay on both triangular sides
and across the final lower and upper factors. No absolute upper or lower
bound is imposed on the positive base entries or diagonal. -/
theorem relative_full_positive_factorization_iff {p q : ℕ}
    (a : Fin (p+1) → ℕ → ℝ) (d : ℕ → ℝ) (b : Fin (q+1) → ℕ → ℝ)
    (ha : ∀ i n,0<a i n) (hd : ∀ n,0<d n) (hb : ∀ i n,0<b i n) :
    RelativeFullPositiveAnalyticChoice a d b ha hd hb ↔
      RelativeAdjacentGeometric a ∧ RelativeAdjacentGeometric b ∧
      GeometricDecay (crossWeight (a ⟨p,by omega⟩) (b ⟨q,by omega⟩) d) := by
  constructor
  · intro hc
    have hp := relative_full_choice_implies_adjacent_of_ldu_injective a d b ha hd hb
      (relative_factor_ldu_derivative_injective a d b ha hd hb) hc
    exact ⟨hp.1,hp.2,relative_full_positive_choice_implies_cross a d b ha hd hb hc⟩
  · rintro ⟨hga,hgb,hcross⟩
    exact relative_full_positive_of_ldu_and_adjacent a d b ha hd hb hga hgb
      (relative_factor_ldu_analytic_of_geometric a d b ha hd hb hga hgb hcross)

/-- The same exact criterion yields a locally Lipschitz map in the uniform
norm of relative changes, for all entries of all factors simultaneously. -/
theorem relative_full_positive_factorization_with_lipschitz {p q : ℕ}
    (a : Fin (p+1) → ℕ → ℝ) (d : ℕ → ℝ) (b : Fin (q+1) → ℕ → ℝ)
    (ha : ∀ i n,0<a i n) (hd : ∀ n,0<d n) (hb : ∀ i n,0<b i n)
    (hga : RelativeAdjacentGeometric a) (hgb : RelativeAdjacentGeometric b)
    (hcross : GeometricDecay (crossWeight (a ⟨p,by omega⟩) (b ⟨q,by omega⟩) d)) :
    ∃ g : FullBand (p+1) (q+1) → FullBand (p+1) (q+1),
      AnalyticAt ℝ g 0 ∧ g 0=0 ∧
      (∀ᶠ E in 𝓝 (0 : FullBand (p+1) (q+1)),relativeFullProduct a d b ha hd hb (g E)=E ∧
        (∀ i n,1≤n → 0<relativePerturbedFactor a (g E).1 i n) ∧
        (∀ i n,1≤n → 0<relativePerturbedFactor b (g E).2.2 i n) ∧
        (∀ n,0<d n*(1+(g E).2.1 n)) ∧
        (∀ i n,n<p+1-i.val → relativePerturbedFactor a (g E).1 i n=a i n) ∧
        (∀ i n,n<q+1-i.val → relativePerturbedFactor b (g E).2.2 i n=b i n)) ∧
      ∃ K,∃ s ∈ 𝓝 (0 : FullBand (p+1) (q+1)),LipschitzOnWith K g s :=
  relative_full_choice_with_lipschitz a d b ha hd hb
    ((relative_full_positive_factorization_iff a d b ha hd hb).mpr ⟨hga,hgb,hcross⟩)

#print axioms relative_factor_ldu_derivative_injective
#print axioms relative_factor_ldu_analytic_of_geometric
#print axioms relative_full_positive_factorization_iff
#print axioms relative_full_positive_factorization_with_lipschitz
end BTP.RelativeStability
