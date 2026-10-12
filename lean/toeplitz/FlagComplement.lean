import UnrestrictedDeterminant
import BandStructure

/-! Complementary corner minors. The permutation sign is kept as the
determinant of a fixed permutation matrix, and is calibrated below. -/

open Matrix Finset
noncomputable section
set_option linter.unusedSimpArgs false
namespace BTP.SemiInfinite
open Extraction InverseBounds

def corner (F : NatMatrix) (k n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => F (k+i.val) j.val

def replaceInitialRows (A : Matrix (Fin (n+k)) (Fin (n+k)) ℝ) :
    Matrix (Fin (n+k)) (Fin (n+k)) ℝ := fun i j =>
  if h : i.val < n then A ⟨k+i.val, by omega⟩ j else (1 : Matrix _ _ ℝ) i j

theorem replaceInitialRows_det (A : Matrix (Fin (n+k)) (Fin (n+k)) ℝ) :
    (replaceInitialRows A).det =
      (A.submatrix (fun i : Fin n => ⟨k+i.val, by omega⟩)
        (fun j : Fin n => ⟨j.val, by omega⟩)).det := by
  let B : Matrix (Fin n) (Fin k) ℝ := fun i j => A ⟨k+i.val, by omega⟩ (Fin.natAdd n j)
  let C := A.submatrix (fun i : Fin n => ⟨k+i.val, by omega⟩)
        (fun j : Fin n => ⟨j.val, by omega⟩)
  have he : (replaceInitialRows A).submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks C B 0 1 := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · simp [replaceInitialRows, C, Matrix.submatrix, i.isLt]
      rfl
    · simp [replaceInitialRows, B, Matrix.submatrix, Matrix.fromBlocks, i.isLt]
    · simp [replaceInitialRows, Matrix.submatrix, Matrix.one_apply, Fin.ext_iff,
        show ¬ n+i.val < n by omega, show n+i.val ≠ j.val by omega]
    · simp [replaceInitialRows, Matrix.submatrix, Matrix.one_apply, Fin.ext_iff,
        show ¬ n+i.val < n by omega]
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv (replaceInitialRows A), he,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]

def cornerRowEquiv (n k : ℕ) : Fin k ⊕ Fin n ≃ Fin (n+k) :=
  (Equiv.sumComm _ _).trans finSumFinEquiv

def cornerColEquiv (n k : ℕ) : Fin k ⊕ Fin n ≃ Fin (n+k) :=
  finSumFinEquiv.trans (finCongr (Nat.add_comm k n))

def cornerPermutation (n k : ℕ) : ℝ :=
  ((1 : Matrix (Fin (n+k)) (Fin (n+k)) ℝ).submatrix
    (cornerRowEquiv n k) (cornerColEquiv n k)).det

theorem determinant_two_equivs (A : Matrix (Fin (n+k)) (Fin (n+k)) ℝ) :
    (A.submatrix (cornerRowEquiv n k) (cornerColEquiv n k)).det =
      cornerPermutation n k * A.det := by
  have he : A.submatrix (cornerRowEquiv n k) (cornerColEquiv n k) =
      (1 : Matrix (Fin (n+k)) (Fin (n+k)) ℝ).submatrix
        (cornerRowEquiv n k) (cornerColEquiv n k) *
      A.submatrix (cornerColEquiv n k) (cornerColEquiv n k) := by
    rw [Matrix.submatrix_mul_equiv]
    simp
  rw [he, Matrix.det_mul, Matrix.det_submatrix_equiv_self]
  rfl

theorem inverse_corner_up_to_sign (A : Matrix (Fin (n+k)) (Fin (n+k)) ℝ)
    (hA : A.det = 1) :
    (A⁻¹.submatrix (fun i : Fin k => ⟨n+i.val, by omega⟩)
        (fun j : Fin k => ⟨j.val, by omega⟩)).det =
      cornerPermutation n k *
        (A.submatrix (fun i : Fin n => ⟨k+i.val, by omega⟩)
          (fun j : Fin n => ⟨j.val, by omega⟩)).det := by
  let V := replaceInitialRows A * A⁻¹
  have hV (i j : Fin (n+k)) : V i j =
      if h : i.val < n then (1 : Matrix (Fin (n+k)) (Fin (n+k)) ℝ)
        ⟨k+i.val, by omega⟩ j else A⁻¹ i j := by
    dsimp [V]
    rw [Matrix.mul_apply]
    by_cases hi : i.val < n
    · simp only [replaceInitialRows, hi, dite_true]
      exact congrArg (fun M : Matrix (Fin (n+k)) (Fin (n+k)) ℝ =>
        M ⟨k+i.val, by omega⟩ j) (Matrix.mul_nonsing_inv A (by rw [hA]; exact isUnit_one))
    · simp only [replaceInitialRows, hi, dite_false]
      exact congrArg (fun M : Matrix (Fin (n+k)) (Fin (n+k)) ℝ => M i j)
        (Matrix.one_mul A⁻¹)
  let C := A⁻¹.submatrix (fun i : Fin k => ⟨n+i.val, by omega⟩)
        (fun j : Fin k => ⟨j.val, by omega⟩)
  let B : Matrix (Fin k) (Fin n) ℝ :=
    fun i j => A⁻¹ ⟨n+i.val, by omega⟩ ⟨k+j.val, by omega⟩
  have he : V.submatrix (cornerRowEquiv n k) (cornerColEquiv n k) =
      Matrix.fromBlocks C B 0 1 := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · simp [Matrix.submatrix, cornerRowEquiv, cornerColEquiv, hV, C,
        show ¬ n+i.val < n by omega]
      rfl
    · simp [Matrix.submatrix, cornerRowEquiv, cornerColEquiv, hV, B, Matrix.fromBlocks,
        show ¬ n+i.val < n by omega]
      have hj : j.addNat k = (⟨k+j.val, by omega⟩ : Fin (n+k)) := by
        apply Fin.ext; simp; omega
      rw [hj]
      rfl
    · simp [Matrix.submatrix, cornerRowEquiv, cornerColEquiv, hV, i.isLt,
        Matrix.one_apply, Fin.ext_iff, show k+i.val ≠ j.val by omega]
    · simp [Matrix.submatrix, cornerRowEquiv, cornerColEquiv, hV, i.isLt,
        Matrix.one_apply, Fin.ext_iff]
  have hd := determinant_two_equivs (n := n) (k := k) V
  rw [he, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one] at hd
  rw [show V.det = (replaceInitialRows A).det by
    dsimp [V]; rw [Matrix.det_mul, Matrix.det_nonsing_inv, hA]; simp,
    replaceInitialRows_det] at hd
  exact hd

def cornerSign (n k : ℕ) : ℝ :=
  (∏ i : Fin k, (-1 : ℝ)^(n+i.val)) *
  (∏ j : Fin k, (-1 : ℝ)^j.val) * cornerPermutation n k

theorem signed_inverse_corner (F R : NatMatrix)
    (hF : ∀ d, UnitLower d F) (hR : SignedInverse F R) (n k : ℕ) :
    windowDet k (fun t j => R t j.val) n = cornerSign n k * (corner F k n).det := by
  let A := finiteMatrix (n+k) F
  have he : (Matrix.of fun i j : Fin k => R (n+i.val) j.val) =
      fun i j => (-1 : ℝ)^(n+i.val) *
        A⁻¹ ⟨n+i.val, by omega⟩ ⟨j.val, by omega⟩ * (-1 : ℝ)^j.val := by
    ext i j
    have h := congrArg (fun M : Square (n+k) =>
      M ⟨n+i.val, by omega⟩ ⟨j.val, by omega⟩) (hR (n+k))
    simpa [checker_entry, finiteMatrix, A] using h
  unfold windowDet
  rw [he]
  have hs : (fun i j : Fin k => (-1 : ℝ)^(n+i.val) *
        A⁻¹ ⟨n+i.val, by omega⟩ ⟨j.val, by omega⟩ * (-1 : ℝ)^j.val) =
      (fun i j : Fin k => (-1 : ℝ)^(n+i.val) *
        ((-1 : ℝ)^j.val * A⁻¹ ⟨n+i.val, by omega⟩ ⟨j.val, by omega⟩)) := by
    funext i j; ring
  let C : Matrix (Fin k) (Fin k) ℝ :=
    (A⁻¹).submatrix (fun i : Fin k => ⟨n+i.val, by omega⟩)
      (fun j : Fin k => ⟨j.val, by omega⟩)
  have hscale := Matrix.det_mul_column (fun i : Fin k => (-1 : ℝ)^(n+i.val))
    (fun i j : Fin k => (-1 : ℝ)^j.val * C i j)
  have hscale' := Matrix.det_mul_row (fun j : Fin k => (-1 : ℝ)^j.val) C
  change Matrix.det (fun i j : Fin k => (-1 : ℝ)^j.val * C i j) =
    (∏ j : Fin k, (-1 : ℝ)^j.val) * C.det at hscale'
  rw [hscale'] at hscale
  have hc := inverse_corner_up_to_sign A (unitLower_det (hF (n+k)))
  change C.det = cornerPermutation n k * (corner F k n).det at hc
  rw [hc] at hscale
  rw [hs]
  change (Matrix.of (fun i j : Fin k => (-1 : ℝ)^(n+i.val) *
    ((-1 : ℝ)^j.val * C i j))).det = _
  rw [hscale]
  unfold cornerSign
  ring

theorem product_signedInverse (a : Entries) (p : ℕ) :
    SignedInverse (productEntries a p) (inverseEntries a p) := by
  intro d
  rw [product_finite]
  ext i j
  exact signed_inverse_section d p a i j

theorem ones_extreme_entry (k n : ℕ) : entry (fun _ _ => 1) k n k = 1 := by
  induction k generalizing n with
  | zero => simp [entry]
  | succ k ih => rw [entry_diag_step, ih]; simp

theorem ones_corner_det (n k : ℕ) :
    (corner (productEntries (fun _ _ => 1) k) k n).det = 1 := by
  have hu : (corner (productEntries (fun _ _ => 1) k) k n).IsUpperTriangular := by
    intro i j hij
    exact product_band (k+n+1) (fun _ _ => 1) k (k+i.val) (by omega)
      j.val (by omega) (by change j.val < i.val at hij; omega)
  rw [Matrix.det_of_isUpperTriangular hu]
  apply prod_eq_one
  intro i _
  simp only [corner, productEntries, ite_eq_left (show i.val ≤ k+i.val by omega),
    show k+i.val-i.val = k by omega, ones_extreme_entry]

theorem ones_inverse_window (n k : ℕ) :
    windowDet k (fun t j => inverseEntries (fun _ _ => 1) k t j.val) n = 1 := by
  cases k with
  | zero => simp [windowDet]
  | succ k =>
    have hF := fun d => product_unit d (fun _ _ => 1) (k+1)
    have hR := product_signedInverse (fun _ _ => 1) (k+1)
    induction n with
    | zero =>
      have h := extraction_initial_determinant (m := k+2) hF hR (fun _ => 0)
      simpa [windowDet, extractionColumns] using h
    | succ n ih =>
      rw [inverse_window_det hF hR k n (product_band _ _ _), ih]
      simp [productEntries, show n ≤ n+k+1 by omega,
        show n+k+1-n = k+1 by omega, ones_extreme_entry]

theorem cornerSign_one (n k : ℕ) : cornerSign n k = 1 := by
  have h := signed_inverse_corner (productEntries (fun _ _ => 1) k)
    (inverseEntries (fun _ _ => 1) k) (fun d => product_unit d _ k)
    (product_signedInverse _ k) n k
  rw [ones_inverse_window, ones_corner_det, mul_one] at h
  exact h.symm

/-- The signed inverse flag minor is exactly the complementary minor of F.
For a BTP lower triangular F of bandwidth p, the right side is positive
whenever k ≤ p. -/
theorem inverse_flag_complement (F R : NatMatrix)
    (hF : ∀ d, UnitLower d F) (hR : SignedInverse F R) (n k : ℕ) :
    windowDet k (fun t j => R t j.val) n = (corner F k n).det := by
  rw [signed_inverse_corner F R hF hR, cornerSign_one, one_mul]

#print axioms inverse_flag_complement
end BTP.SemiInfinite
