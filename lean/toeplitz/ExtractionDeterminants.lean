import UniformMinors

/-! # Consecutive determinants and extraction

This file starts with the discrete Abel identity, proved by multilinearity
and the sign of a cyclic row permutation.
-/
open Matrix Finset
noncomputable section
namespace BTP.SemiInfinite
open InverseBounds Extraction

/-- Determinant of d consecutive row vectors. -/
def windowDet (d : ℕ) (v : ℕ → Fin d → ℝ) (n : ℕ) : ℝ :=
  (Matrix.of fun i j : Fin d => v (n + i.val) j).det

theorem windowDet_shift {d n : ℕ} (v : ℕ → Fin (d + 1) → ℝ)
    (c : Fin (d + 1) → ℝ)
    (hrec : v (n + d + 1) = ∑ i : Fin (d + 1), c i • v (n + i.val)) :
    windowDet (d + 1) v (n + 1) =
      (-1 : ℝ) ^ d * c 0 * windowDet (d + 1) v n := by
  let A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ := fun i j => v (n + i.val) j
  let B := A.updateRow 0 (∑ i : Fin (d + 1), c i • A i)
  have hmatrix : (Matrix.of fun i j : Fin (d + 1) => v (n + 1 + i.val) j) =
      B.submatrix (finRotate (d + 1)) id := by
    ext i j
    induction i using Fin.lastCases with
    | last =>
      change v (n + 1 + d) j = B (finRotate (d + 1) (Fin.last d)) j
      rw [finRotate_last]
      change v (n + 1 + d) j = (A.updateRow 0 (∑ i, c i • A i)) 0 j
      rw [Matrix.updateRow_self]
      have hv := congrFun hrec j
      simpa only [A, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        show n + 1 + d = n + d + 1 by omega] using hv
    | cast i =>
      have hne : i.castSucc ≠ Fin.last d := by
        intro h; have := congrArg Fin.val h; simp only [Fin.val_castSucc, Fin.val_last] at this; omega
      have hrot : finRotate (d + 1) i.castSucc = i.succ := by
        apply Fin.ext
        exact coe_finRotate_of_ne_last hne
      change v (n + 1 + i.val) j = (A.updateRow 0 (∑ i, c i • A i))
        (finRotate (d + 1) i.castSucc) j
      rw [hrot, Matrix.updateRow_ne i.succ_ne_zero]
      change v (n + 1 + i.val) j = v (n + (i.val + 1)) j
      congr 1
      omega
  unfold windowDet
  rw [hmatrix, Matrix.det_permute, Matrix.det_updateRow_sum]
  simp only [sign_finRotate, Nat.add_sub_cancel, Units.val_pow_eq_pow_val, Units.val_neg,
    Units.val_one, Int.cast_pow, Int.cast_neg, Int.cast_one, smul_eq_mul]
  change (-1 : ℝ)^d * (c 0 * A.det) = (-1 : ℝ)^d * c 0 * A.det
  ring

/-- Exact compatibility with the inverses of all finite leading sections. -/
def SignedInverse (F R : NatMatrix) : Prop :=
  ∀ d, finiteMatrix d R = checker ((finiteMatrix d F)⁻¹)

theorem unitLower_det {d : ℕ} {F : NatMatrix} (hF : UnitLower d F) :
    (finiteMatrix d F).det = 1 := by
  have hlow : (finiteMatrix d F).IsLowerTriangular := by
    intro i j hij
    exact hF.2 i i.isLt j j.isLt hij
  calc
    (finiteMatrix d F).det = ∏ i, finiteMatrix d F i i := Matrix.det_of_isLowerTriangular _ hlow
    _ = 1 := prod_eq_one (fun i _ => hF.1 i i.isLt)

theorem signedInverse_equation {F R : NatMatrix}
    (hF : ∀ d, UnitLower d F) (hR : SignedInverse F R) (d : ℕ) :
    checker (finiteMatrix d F) * finiteMatrix d R = 1 := by
  rw [hR d, ← checker_mul, Matrix.mul_nonsing_inv _ (by rw [unitLower_det (hF d)]; exact isUnit_one),
    checker_one]

/-- The inverse row at n+d is a linear combination of the preceding d rows. -/
theorem inverse_window_row {F R : NatMatrix} (hF : ∀ d, UnitLower d F)
    (hR : SignedInverse F R) {d : ℕ} (n : ℕ) (hb : Bandwidth (n + d + 1) d F) :
    (fun j : Fin d => R (n + d) j.val) =
      ∑ i : Fin d, (-( (-1 : ℝ) ^ (n + d) * F (n + d) (n + i.val) *
        (-1 : ℝ) ^ (n + i.val))) • (fun j : Fin d => R (n + i.val) j.val) := by
  funext j
  let t := n + d
  have hjt : j.val < t := by dsimp [t]; omega
  have heq := congrArg
    (fun M : Square (t + 1) => M ⟨t, by omega⟩ ⟨j.val, by omega⟩)
    (signedInverse_equation hF hR (t + 1))
  rw [Matrix.mul_apply] at heq
  simp only [checker_entry, finiteMatrix, Matrix.of_apply, Matrix.one_apply] at heq
  have hne : (⟨t, by omega⟩ : Fin (t + 1)) ≠ ⟨j.val, by omega⟩ := by
    intro h; have := congrArg Fin.val h; dsimp at this; omega
  rw [ite_eq_right hne] at heq
  rw [Fin.sum_univ_eq_sum_range (fun h : ℕ => (-1 : ℝ)^t * F t h * (-1 : ℝ)^h * R h j.val)] at heq
  rw [sum_range_succ] at heq
  have hdiag : F t t = 1 := (hF (t + 1)).1 t (by omega)
  rw [hdiag, mul_one, sign_square, one_mul] at heq
  have hprefix : (∑ h ∈ range n, (-1 : ℝ) ^ t * F t h * (-1 : ℝ) ^ h * R h j.val) = 0 := by
    apply sum_eq_zero
    intro h hh
    rw [hb t (by omega) h (by have := mem_range.mp hh; omega)
      (by have := mem_range.mp hh; dsimp [t]; omega)]
    ring
  have hsum : (∑ h ∈ range t, (-1 : ℝ) ^ t * F t h * (-1 : ℝ) ^ h * R h j.val) =
      ∑ i : Fin d, (-1 : ℝ) ^ t * F t (n + i.val) * (-1 : ℝ) ^ (n + i.val) * R (n + i.val) j.val := by
    rw [← sum_range_add_sum_Ico _ (show n ≤ t by dsimp [t]; omega), hprefix, zero_add,
      sum_Ico_eq_sum_range]
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => (-1 : ℝ)^t * F t (n+i) * (-1 : ℝ)^(n+i) * R (n+i) j.val)]
    simp only [t, Nat.add_sub_cancel_left]
  rw [hsum] at heq
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, neg_mul]
  rw [sum_neg_distrib]
  dsimp [t] at heq
  linarith

/-- Discrete Abel identity for the signed inverse of a unit triangular band matrix. -/
theorem inverse_window_det {F R : NatMatrix} (hF : ∀ D, UnitLower D F)
    (hR : SignedInverse F R) (d n : ℕ) (hb : Bandwidth (n + d + 2) (d + 1) F) :
    windowDet (d + 1) (fun t j => R t j.val) (n + 1) =
      F (n + d + 1) n * windowDet (d + 1) (fun t j => R t j.val) n := by
  have hr := inverse_window_row hF hR (d := d + 1) n (by simpa only [Nat.add_assoc] using hb)
  have hw := windowDet_shift (n := n) (fun t j => R t j.val)
    (fun i : Fin (d + 1) => -((-1 : ℝ) ^ (n + d + 1) * F (n + d + 1) (n + i.val) *
      (-1 : ℝ) ^ (n + i.val))) (by simpa only [Nat.add_assoc] using hr)
  rw [hw]
  simp only [Fin.val_zero, Nat.add_zero, pow_succ, pow_add]
  have hn := sign_square n
  have hd := sign_square d
  calc
    _ = ((-1 : ℝ)^n * (-1)^n) * ((-1 : ℝ)^d * (-1)^d) *
      (F (n + d + 1) n * windowDet (d + 1) (fun t j => R t j.val) n) := by ring
    _ = _ := by rw [hn, hd]; ring

#print axioms windowDet_shift
#print axioms inverse_window_det
end BTP.SemiInfinite
