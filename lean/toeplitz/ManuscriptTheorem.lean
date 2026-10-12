import ToeplitzTheorem

/-! The manuscript's original coefficients t : ℤ -> ℝ and its band endpoints.
The matrix convention is literally T[i,j] = t(i-j), with indices starting at 0.
-/

open Polynomial Matrix Finset
noncomputable section
namespace BTP.Toeplitz

structure ToeplitzData (p q : ℕ) where
  t : ℤ → ℝ
  outside : ∀ k, k < -(q : ℤ) ∨ (p : ℤ) < k → t k = 0
  first_pos : 0 < t (-(q : ℤ))
  last_pos : 0 < t (p : ℤ)

def ToeplitzData.matrix {p q : ℕ} (D : ToeplitzData p q) : Matrix ℕ ℕ ℝ :=
  fun i j => D.t ((i : ℤ) - j)

def ToeplitzData.polynomial {p q : ℕ} (D : ToeplitzData p q) : ℝ[X] :=
  ∑ k ∈ range (p+q+1), monomial k (D.t ((k : ℤ) - q))

theorem ToeplitzData.coeff_polynomial {p q : ℕ} (D : ToeplitzData p q) (r : ℕ) :
    D.polynomial.coeff r = if r ≤ p+q then D.t ((r : ℤ) - q) else 0 := by
  simp [ToeplitzData.polynomial, Polynomial.finsetSum_coeff, coeff_monomial,
    Finset.sum_ite_eq']

theorem ToeplitzData.polynomial_zero_pos {p q : ℕ} (D : ToeplitzData p q) :
    0 < D.polynomial.coeff 0 := by
  simpa [D.coeff_polynomial] using D.first_pos

theorem ToeplitzData.polynomial_degree {p q : ℕ} (D : ToeplitzData p q) :
    D.polynomial.natDegree = p+q := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    rw [D.coeff_polynomial, ite_eq_right (by omega)]
  · rw [D.coeff_polynomial, ite_eq_left le_rfl]
    simpa using D.last_pos.ne'

theorem ToeplitzData.symbol_matrix {p q : ℕ} (D : ToeplitzData p q) :
    symbolMatrix q D.polynomial = D.matrix := by
  ext i j
  simp only [symbolMatrix, ToeplitzData.matrix]
  by_cases hj : j ≤ i+q
  · rw [ite_eq_left hj, D.coeff_polynomial]
    have he : ((i+q-j : ℕ) : ℤ) - q = (i : ℤ) - j := by omega
    rw [he]
    by_cases hi : i+q-j ≤ p+q
    · rw [ite_eq_left hi]
    · rw [ite_eq_right hi]
      exact (D.outside _ (Or.inr (by omega))).symm
  · rw [ite_eq_right hj]
    exact (D.outside _ (Or.inl (by omega))).symm

def MatrixPBF (p q : ℕ) (M : Matrix ℕ ℕ ℝ) : Prop :=
  ∃ A : Op, HasPBF p q A ∧ opMatrix A = M

def MatrixBoundedPBF (p q : ℕ) (M : Matrix ℕ ℕ ℝ) : Prop :=
  ∃ A : Op, HasBoundedPBF p q A ∧ opMatrix A = M

theorem matrixPBF_implies_TN {p q : ℕ} {M : Matrix ℕ ℕ ℝ} (h : MatrixPBF p q M) : TN M := by
  obtain ⟨A, ha, rfl⟩ := h
  exact PBF_implies_TN ha

theorem matrixBoundedPBF_implies_PBF {p q : ℕ} {M : Matrix ℕ ℕ ℝ}
    (h : MatrixBoundedPBF p q M) : MatrixPBF p q M := by
  obtain ⟨A, ha, he⟩ := h
  exact ⟨A, ha.hasPBF, he⟩

/-- Exact manuscript coefficients; this constructive theorem has no classical-input argument. -/
theorem manuscript_negative_roots_to_PBF {p q : ℕ} (D : ToeplitzData p q)
    (hroot : NegativeRoots D.polynomial) :
    MatrixBoundedPBF p q D.matrix ∧ StrictBandTP p q D.matrix ∧ TN D.matrix := by
  obtain ⟨hb, _, ht, hn⟩ := negative_roots_to_global_PBF p q D.polynomial
    D.polynomial_degree D.polynomial_zero_pos hroot
  rw [D.symbol_matrix] at ht hn
  refine ⟨⟨symbolOperator q D.polynomial, hb, ?_⟩, ht, hn⟩
  rw [symbolOperator_matrix, D.symbol_matrix]

/-- The entire equivalence in Theorem 3.2, conditional only on the stated
polynomial consequence of Edrei. All other steps are proved in this package. -/
theorem manuscript_theorem_3_2_given_Edrei (hEdrei : EdreiPolynomialInput)
    {p q : ℕ} (D : ToeplitzData p q) :
    (TN D.matrix ↔ StrictBandTP p q D.matrix) ∧
    (TN D.matrix ↔ NegativeRoots D.polynomial) ∧
    (TN D.matrix ↔ MatrixPBF p q D.matrix) ∧
    (TN D.matrix ↔ MatrixBoundedPBF p q D.matrix) := by
  have h := theorem_3_2_given_Edrei hEdrei p q D.polynomial
    D.polynomial_degree D.polynomial_zero_pos
  rw [D.symbol_matrix] at h
  refine ⟨h.1, h.2.1, ⟨?_, matrixPBF_implies_TN⟩,
    ⟨?_, fun hb => matrixPBF_implies_TN (matrixBoundedPBF_implies_PBF hb)⟩⟩
  · intro ht
    exact matrixBoundedPBF_implies_PBF (manuscript_negative_roots_to_PBF D (h.2.1.mp ht)).1
  · intro ht
    exact (manuscript_negative_roots_to_PBF D (h.2.1.mp ht)).1

#print axioms manuscript_negative_roots_to_PBF
#print manuscript_theorem_3_2_given_Edrei
#print axioms manuscript_theorem_3_2_given_Edrei
end BTP.Toeplitz
