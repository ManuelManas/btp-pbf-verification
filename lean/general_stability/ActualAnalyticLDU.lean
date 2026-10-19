import AnalyticLDUCriterion
import AnalyticLDUDerivativeMatrix

/-! The complete normalized-LDU criterion for products of actual bounded
positive bidiagonal factors. The derivative identification is proved from
matrix multiplication; it is no longer a hypothesis of the criterion. -/

noncomputable section
open Finset Filter
open scoped Topology BigOperators
namespace BTP.Stability.BandLDU
open BTP BTP.InverseBounds BTP.SemiInfinite BTP.GeneralStability

theorem actualBase_derivative (a b : Entries) (p q : ℕ) (d : Seq)
    (hd : ∀ n, d n≠0) (M : ℝ) (hM : 0≤M)
    (haM : ∀ k<p, ∀ n, 0<n → |a k n|≤M)
    (hbM : ∀ k<q, ∀ n, 0<n → |b k n|≤M) :
    (actualData a b p q d hd).IsDerivative
      (lduProductDerivative (actualBase a b p q d M hM haM hbM)) := by
  intro E N
  rw [lduProductDerivative_section]
  rw [←actualBase_lower a b p q d M hM haM hbM,
      ←actualBase_upper a b p q d M hM haM hbM]
  rfl

/-- A differentiable local choice of normalized LDU exists exactly when
its nonnegative inverse rows have uniformly bounded joint sums. Under
these equivalent conditions the choice is in fact real analytic. -/
theorem actual_ldu_analytic_iff_row_bound (a b : Entries) (p q : ℕ) (d : Seq)
    (hd : ∀ n, d n≠0) {β M D : ℝ} (hβ : 0<β) (hβ1 : β≤1)
    (hM : 0≤M) (hD : 0≤D)
    (ha : ∀ k<p+1, ∀ n, 0<n → β≤a k n)
    (hb : ∀ k<q+1, ∀ n, 0<n → β≤b k n)
    (haM : ∀ k<p+1, ∀ n, 0<n → |a k n|≤M)
    (hbM : ∀ k<q+1, ∀ n, 0<n → |b k n|≤M)
    (hdD : ∀ n, |(d n)⁻¹|≤D) :
    AnalyticLDUSection (actualBase a b (p+1) (q+1) d M hM haM hbM) ↔
    ∃ Z : ℝ, ∀ n, ∑ s ∈ range (n+1),
      inverseEntries a (p+1) n s*inverseEntries b (q+1) n s≤Z := by
  exact analytic_ldu_iff_row_bound a b p q d hd hβ hβ1 hM hD ha hb haM hbM hdD
    _ (actualBase_derivative a b (p+1) (q+1) d hd M hM haM hbM)

theorem actual_ldu_differentiable_iff_row_bound (a b : Entries) (p q : ℕ) (d : Seq)
    (hd : ∀ n, d n≠0) {β M D : ℝ} (hβ : 0<β) (hβ1 : β≤1)
    (hM : 0≤M) (hD : 0≤D)
    (ha : ∀ k<p+1, ∀ n, 0<n → β≤a k n)
    (hb : ∀ k<q+1, ∀ n, 0<n → β≤b k n)
    (haM : ∀ k<p+1, ∀ n, 0<n → |a k n|≤M)
    (hbM : ∀ k<q+1, ∀ n, 0<n → |b k n|≤M)
    (hdD : ∀ n, |(d n)⁻¹|≤D) :
    DifferentiableLDUSection (actualBase a b (p+1) (q+1) d M hM haM hbM) ↔
    ∃ Z : ℝ, ∀ n, ∑ s ∈ range (n+1),
      inverseEntries a (p+1) n s*inverseEntries b (q+1) n s≤Z := by
  exact differentiable_ldu_iff_row_bound a b p q d hd hβ hβ1 hM hD ha hb haM hbM hdD
    _ (actualBase_derivative a b (p+1) (q+1) d hd M hM haM hbM)

/-- The analytic normalized LDU choice is a unique local inverse, and is
Lipschitz in the uniform norm on the fixed finite collection of diagonals. -/
theorem actual_ldu_local_inverse (a b : Entries) (p q : ℕ) (d : Seq)
    (hd : ∀ n, d n≠0) {β M D Z : ℝ} (hβ : 0<β) (hβ1 : β≤1)
    (hM : 0≤M) (hD : 0≤D)
    (ha : ∀ k<p+1, ∀ n, 0<n → β≤a k n)
    (hb : ∀ k<q+1, ∀ n, 0<n → β≤b k n)
    (haM : ∀ k<p+1, ∀ n, 0<n → |a k n|≤M)
    (hbM : ∀ k<q+1, ∀ n, 0<n → |b k n|≤M)
    (hdD : ∀ n, |(d n)⁻¹|≤D)
    (hrows : ∀ n, ∑ s ∈ range (n+1), inverseEntries a (p+1) n s*inverseEntries b (q+1) n s≤Z) :
    let x := actualBase a b (p+1) (q+1) d M hM haM hbM
    ∃ g : FullBand (p+1) (q+1) → FullBand (p+1) (q+1),
      AnalyticAt ℝ g (lduProduct x) ∧ g (lduProduct x)=x ∧
      (∀ᶠ y in 𝓝 (lduProduct x), lduProduct (g y)=y) ∧
      (∀ᶠ y in 𝓝 x, g (lduProduct y)=y) ∧
      ∃ K, ∃ s ∈ 𝓝 (lduProduct x), LipschitzOnWith K g s := by
  exact analytic_ldu_local_inverse a b p q d hd hβ hβ1 hM hD ha hb haM hbM hdD
    _ (actualBase_derivative a b (p+1) (q+1) d hd M hM haM hbM) hrows

#print axioms actual_ldu_analytic_iff_row_bound
#print axioms actual_ldu_differentiable_iff_row_bound
#print axioms actual_ldu_local_inverse
end BTP.Stability.BandLDU
