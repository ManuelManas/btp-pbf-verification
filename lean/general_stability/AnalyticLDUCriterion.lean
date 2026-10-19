import LDUCriterion
import AnalyticLDUDerivative

/-! Banach analytic inversion of normalized LDU from its genuine
joint signed-inverse row sums. -/
noncomputable section
open Matrix Finset Filter
open scoped BigOperators Topology
namespace BTP.Stability.BandLDU
open BTP BTP.SemiInfinite BTP.GeneralStability BTP.AnalyticFactorization

def AnalyticLDUSection {p q : ℕ} (x : FullBand p q) : Prop :=
  ∃ g : FullBand p q → FullBand p q,
    AnalyticAt ℝ g (lduProduct x) ∧ g (lduProduct x)=x ∧
      ∀ᶠ y in 𝓝 (lduProduct x), lduProduct (g y)=y

def DifferentiableLDUSection {p q : ℕ} (x : FullBand p q) : Prop :=
  ∃ g : FullBand p q → FullBand p q,
    DifferentiableAt ℝ g (lduProduct x) ∧ g (lduProduct x)=x ∧
      ∀ᶠ y in 𝓝 (lduProduct x), lduProduct (g y)=y

theorem analytic_ldu_iff_row_bound (a b : Entries) (p q : ℕ) (d : ℕ → ℝ)
    (hd : ∀ n, d n≠0) {β M D : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hM : 0 ≤ M) (hD : 0 ≤ D)
    (ha : ∀ k < p+1, ∀ t, 0 < t → β ≤ a k t)
    (hb : ∀ k < q+1, ∀ t, 0 < t → β ≤ b k t)
    (haM : ∀ k < p+1, ∀ t, 0 < t → |a k t| ≤ M)
    (hbM : ∀ k < q+1, ∀ t, 0 < t → |b k t| ≤ M)
    (hdD : ∀ n, |(d n)⁻¹| ≤ D)
    (x : FullBand (p+1) (q+1))
    (hA : (actualData a b (p+1) (q+1) d hd).IsDerivative (lduProductDerivative x)) :
    AnalyticLDUSection x ↔ ∃ Z : ℝ, ∀ n, ∑ s ∈ range (n+1),
      inverseEntries a (p+1) n s*inverseEntries b (q+1) n s ≤ Z := by
  constructor
  · rintro ⟨g,hg,hgx,hsection⟩
    let B := fderiv ℝ g (lduProduct x)
    have hB : HasFDerivAt g B (lduProduct x) := hg.differentiableAt.hasFDerivAt
    have hright := derivative_right_inverse_of_section
      (lduProduct_hasFDerivAt x) hB hgx hsection
    let F := B (identityBand (p+1) (q+1))
    refine ⟨‖F‖, actual_row_bound_of_identity_solution a b (p+1) (q+1) d hd
      (lduProductDerivative x) hA F ?_⟩
    exact congrArg (fun C : FullBand (p+1) (q+1) →L[ℝ] FullBand (p+1) (q+1) =>
      C (identityBand (p+1) (q+1))) hright
  · intro hrows
    obtain ⟨J,hJ⟩ := (ldu_derivative_row_criterion a b p q d hd hβ hβ1 hM hD
      ha hb haM hbM hdD (lduProductDerivative x) hA).mpr hrows
    have hJA : (J : FullBand (p+1) (q+1) →L[ℝ] FullBand (p+1) (q+1))=
        lduProductDerivative x := by
      apply ContinuousLinearMap.ext
      intro E
      exact hJ E
    have hder : HasFDerivAt (@lduProduct (p+1) (q+1))
        (J : FullBand (p+1) (q+1) →L[ℝ] FullBand (p+1) (q+1)) x := by
      rw [hJA]
      exact lduProduct_hasFDerivAt x
    obtain ⟨g,hg,hgx,hgR,_⟩ := analytic_local_inverse (analytic_lduProduct x) J hder
    exact ⟨g,hg,hgx,hgR⟩

theorem differentiable_ldu_iff_row_bound (a b : Entries) (p q : ℕ) (d : ℕ → ℝ)
    (hd : ∀ n, d n≠0) {β M D : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hM : 0 ≤ M) (hD : 0 ≤ D)
    (ha : ∀ k < p+1, ∀ t, 0 < t → β ≤ a k t)
    (hb : ∀ k < q+1, ∀ t, 0 < t → β ≤ b k t)
    (haM : ∀ k < p+1, ∀ t, 0 < t → |a k t| ≤ M)
    (hbM : ∀ k < q+1, ∀ t, 0 < t → |b k t| ≤ M)
    (hdD : ∀ n, |(d n)⁻¹| ≤ D)
    (x : FullBand (p+1) (q+1))
    (hA : (actualData a b (p+1) (q+1) d hd).IsDerivative (lduProductDerivative x)) :
    DifferentiableLDUSection x ↔ ∃ Z : ℝ, ∀ n, ∑ s ∈ range (n+1),
      inverseEntries a (p+1) n s*inverseEntries b (q+1) n s ≤ Z := by
  constructor
  · rintro ⟨g,hg,hgx,hsection⟩
    let B := fderiv ℝ g (lduProduct x)
    have hB : HasFDerivAt g B (lduProduct x) := hg.hasFDerivAt
    have hright := derivative_right_inverse_of_section
      (lduProduct_hasFDerivAt x) hB hgx hsection
    let F := B (identityBand (p+1) (q+1))
    refine ⟨‖F‖, actual_row_bound_of_identity_solution a b (p+1) (q+1) d hd
      (lduProductDerivative x) hA F ?_⟩
    exact congrArg (fun C : FullBand (p+1) (q+1) →L[ℝ] FullBand (p+1) (q+1) =>
      C (identityBand (p+1) (q+1))) hright
  · intro hrows
    obtain ⟨g,hg,hgx,hgR⟩ := (analytic_ldu_iff_row_bound a b p q d hd hβ hβ1 hM hD
      ha hb haM hbM hdD x hA).mpr hrows
    exact ⟨g,hg.differentiableAt,hgx,hgR⟩

/-- The analytic choice is a genuine local inverse and is Lipschitz on
some neighborhood, in the uniform norm of the complete band sequences. -/
theorem analytic_ldu_local_inverse (a b : Entries) (p q : ℕ) (d : ℕ → ℝ)
    (hd : ∀ n, d n≠0) {β M D Z : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hM : 0 ≤ M) (hD : 0 ≤ D)
    (ha : ∀ k < p+1, ∀ t, 0 < t → β ≤ a k t)
    (hb : ∀ k < q+1, ∀ t, 0 < t → β ≤ b k t)
    (haM : ∀ k < p+1, ∀ t, 0 < t → |a k t| ≤ M)
    (hbM : ∀ k < q+1, ∀ t, 0 < t → |b k t| ≤ M)
    (hdD : ∀ n, |(d n)⁻¹| ≤ D)
    (x : FullBand (p+1) (q+1))
    (hA : (actualData a b (p+1) (q+1) d hd).IsDerivative (lduProductDerivative x))
    (hrows : ∀ n, ∑ s ∈ range (n+1), inverseEntries a (p+1) n s*inverseEntries b (q+1) n s ≤ Z) :
    ∃ g : FullBand (p+1) (q+1) → FullBand (p+1) (q+1),
      AnalyticAt ℝ g (lduProduct x) ∧ g (lduProduct x)=x ∧
      (∀ᶠ y in 𝓝 (lduProduct x), lduProduct (g y)=y) ∧
      (∀ᶠ y in 𝓝 x, g (lduProduct y)=y) ∧
      ∃ K, ∃ s ∈ 𝓝 (lduProduct x), LipschitzOnWith K g s := by
  obtain ⟨J,hJ⟩ := (ldu_derivative_row_criterion a b p q d hd hβ hβ1 hM hD
    ha hb haM hbM hdD (lduProductDerivative x) hA).mpr ⟨Z,hrows⟩
  have hJA : (J : FullBand (p+1) (q+1) →L[ℝ] FullBand (p+1) (q+1))=
      lduProductDerivative x := by
    apply ContinuousLinearMap.ext
    intro E
    exact hJ E
  have hder : HasFDerivAt (@lduProduct (p+1) (q+1))
      (J : FullBand (p+1) (q+1) →L[ℝ] FullBand (p+1) (q+1)) x := by
    rw [hJA]
    exact lduProduct_hasFDerivAt x
  obtain ⟨g,hg,hgx,hgR,hgL⟩ := analytic_local_inverse (analytic_lduProduct x) J hder
  exact ⟨g,hg,hgx,hgR,hgL,hg.hasStrictFDerivAt.exists_lipschitzOnWith⟩

#print axioms analytic_ldu_iff_row_bound
#print axioms differentiable_ldu_iff_row_bound
#print axioms analytic_ldu_local_inverse
end BTP.Stability.BandLDU
