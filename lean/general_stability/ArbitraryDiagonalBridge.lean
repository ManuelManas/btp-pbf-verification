import CompleteSharpResults

/-! The two-sided criterion with an arbitrary positive diagonal in the
candidate PBF. This closes the normalization step explicitly. -/
open Matrix Finset
noncomputable section
namespace BTP.SemiInfinite
open InverseBounds

lemma triangularSections_det (p q : ℕ) (a c : Entries) (D : ℕ → ℝ) (d : ℕ) :
    (triangularSections p q a c D d).det = ∏ i ∈ range d, D i := by
  simp only [triangularSections, Matrix.det_mul, lowerProduct_det,
    Matrix.det_transpose, Matrix.det_diagonal, one_mul, mul_one]
  exact Fin.prod_univ_eq_prod_range D d

/-- Equality of normalized triangular products determines the diagonal,
without presupposing that the two diagonal sequences agree. -/
theorem normalized_diagonal_unique (p q : ℕ) (a b c e : Entries)
    (D E : ℕ → ℝ) (hD : ∀ n, D n ≠ 0)
    (he : ∀ d, triangularSections p q b e E d = triangularSections p q a c D d) :
    E = D := by
  have hprod : ∀ d, (∏ i ∈ range d, E i) = ∏ i ∈ range d, D i := by
    intro d
    simpa only [triangularSections_det] using congrArg Matrix.det (he d)
  funext n
  have h := hprod (n + 1)
  rw [prod_range_succ, prod_range_succ, hprod n] at h
  have hn : (∏ i ∈ range n, D i) ≠ 0 := prod_ne_zero_iff.mpr (fun i _ => hD i)
  exact mul_left_cancel₀ hn h

/-- A candidate PBF may initially have an arbitrary positive diagonal. -/
def HasArbitraryTwoSidedPBF (p q : ℕ) (a c : Entries) (D : ℕ → ℝ) : Prop :=
  ∃ b e : Entries, ∃ E : ℕ → ℝ, Positive p b ∧ Positive q e ∧
    (∀ n, 0 < E n) ∧
    ∀ d, triangularSections p q b e E d = triangularSections p q a c D d

theorem arbitrary_two_sided_iff_normalized (p q : ℕ) (a c : Entries)
    (D : ℕ → ℝ) (hD : ∀ n, 0 < D n) :
    HasArbitraryTwoSidedPBF p q a c D ↔ HasTwoSidedPBF p q a c D := by
  constructor
  · rintro ⟨b,e,E,hb,he,hE,hprod⟩
    have hED := normalized_diagonal_unique p q a b c e D E (fun n => (hD n).ne') hprod
    subst E
    exact ⟨hD,b,e,hb,he,hprod⟩
  · rintro ⟨_,b,e,hb,he,hprod⟩
    exact ⟨b,e,D,hb,he,hD,hprod⟩

/-- The inverse-minor criterion for arbitrary positive bidiagonal
factorizations, with no common-diagonal assumption on a candidate. -/
theorem arbitrary_two_sided_PBF_iff_positive_limits {p q : ℕ}
    (hp : 0 < p) (hq : 0 < q) {a c : Entries} {D : ℕ → ℝ}
    (ha : Metelmann p a) (hc : Metelmann q c) (hD : ∀ n, 0 < D n) :
    HasArbitraryTwoSidedPBF p q a c D ↔
      ∀ i : ObstructionIndex p q, 0 < twoSidedLimit p q a c i := by
  rw [arbitrary_two_sided_iff_normalized p q a c D hD]
  exact two_sided_PBF_iff_positive_limits hp hq ha hc hD

#print axioms normalized_diagonal_unique
#print axioms arbitrary_two_sided_PBF_iff_positive_limits
end BTP.SemiInfinite
