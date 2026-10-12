import ExtractionDeterminants

/-! # Positivity of the determinants implies positivity of every extracted entry

The proof is by induction on the row. It uses finite inverses only after the
preceding recurrence values have been proved positive. In particular, the
positivity of the desired factor is NOT an assumption.
-/
open Matrix Finset
noncomputable section
namespace BTP.SemiInfinite
open InverseBounds Extraction

theorem signedInverse_upper {F R : NatMatrix} (hF : ∀ d, UnitLower d F)
    (hR : SignedInverse F R) {n j : ℕ} (hnj : n < j) : R n j = 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have he := congrArg
      (fun M : Square (j + 1) => M ⟨n, by omega⟩ ⟨j, by omega⟩)
      (signedInverse_equation hF hR (j + 1))
    have hne : (⟨n, by omega⟩ : Fin (j + 1)) ≠ ⟨j, by omega⟩ := by
      intro h; have := congrArg Fin.val h; dsimp at this; omega
    rw [Matrix.mul_apply] at he
    simp only [checker_entry, finiteMatrix, Matrix.of_apply, Matrix.one_apply,
      ite_eq_right hne] at he
    rw [sum_eq_single (⟨n, by omega⟩ : Fin (j + 1))] at he
    · rw [(hF (j + 1)).1 n (by omega), mul_one, sign_square, one_mul] at he
      exact he
    · intro k _ hkn
      have hk : k.val ≠ n := by intro h; apply hkn; exact Fin.ext h
      by_cases hlt : k.val < n
      · rw [ih k.val hlt (by omega)]; ring
      · rw [(hF (j + 1)).2 n (by omega) k.val k.isLt (by omega)]; ring
    · simp

def removedInverse (R : NatMatrix) (a : ℕ → ℝ) (n j : ℕ) : ℝ :=
  R n j - R n (j + 1) * a (j + 1)

theorem removedInverse_finite {F R : NatMatrix} (hF : ∀ d, UnitLower d F)
    (hR : SignedInverse F R) (a : ℕ → ℝ) (d : ℕ) :
    finiteMatrix d (removedInverse R a) = finiteMatrix d R * bidiagonal d (fun n => -a n) := by
  rw [bidiagonal, Matrix.mul_add, Matrix.mul_one]
  ext i j
  simp only [finiteMatrix, Matrix.of_apply, removedInverse, Matrix.add_apply, Matrix.mul_apply]
  by_cases hj : j.val + 1 < d
  · let s : Fin d := ⟨j.val + 1, hj⟩
    rw [sum_eq_single s]
    · simp [s, sub_eq_add_neg]
    · intro k _ hks
      have hk : k.val ≠ j.val + 1 := by intro h; apply hks; exact Fin.ext h
      simp only [ite_eq_right hk, mul_zero]
    · simp
  · have hzero : R i.val (j.val + 1) = 0 := signedInverse_upper hF hR (by omega)
    rw [hzero, zero_mul, sub_zero]
    have hsum : (∑ k : Fin d, R i.val k.val *
        (if k.val = j.val + 1 then -a k.val else 0)) = 0 := by
      apply sum_eq_zero
      intro k _
      have hk : k.val ≠ j.val + 1 := by omega
      simp [hk]
    simp only [hsum, add_zero]

theorem signedInverse_remainder {F R : NatMatrix} (hF : ∀ d, UnitLower d F)
    (hR : SignedInverse F R) (a : ℕ → ℝ) :
    SignedInverse (remainder a F) (removedInverse R a) := by
  intro d
  rw [removedInverse_finite hF hR, remainder_inverse d a F (hF d),
    Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (by rw [bidiagonal_det]; exact isUnit_one),
    checker_mul, ← hR d, checker_bidiagonal]

/-- These are exactly the m-1 columns obtained by multiplying R[:,0:m] by M. -/
def extractionColumns (R : NatMatrix) (θ : ℕ → ℝ) (m : ℕ) (n : ℕ) (j : Fin (m - 1)) : ℝ :=
  R n j.val - θ (j.val + 1) * R n (j.val + 1)

theorem extraction_recurrence_positive {m : ℕ} (hm : 2 ≤ m)
    (F R : NatMatrix) (θ : ℕ → ℝ)
    (hF : ∀ d, UnitLower d F) (hb : ∀ d, Bandwidth d m F)
    (hext : ∀ n, m ≤ n → 0 < F n (n - m)) (hR : SignedInverse F R)
    (hθ : ∀ n, 0 < n → n < m → 0 < θ n)
    (hW : ∀ n, 0 < windowDet (m - 1) (extractionColumns R θ m) n) :
    ∀ n, 0 < canonicalSequence m (by omega) F θ n := by
  let φ := canonicalSequence m (by omega) F θ
  let a := fun n => φ (n - 1) / φ n
  let H := remainder a F
  let S := removedInverse R a
  have ha : ∀ n, 0 < n → n < m → a n = θ n :=
    initial_ratios m (by omega) θ φ (fun n hn hnm => (hθ n hn hnm).ne')
      (canonical_initial m (by omega) F θ)
  have hH : ∀ d, UnitLower d H := fun d => remainder_unit d a F (hF d)
  have hS : SignedInverse H S := signedInverse_remainder hF hR a
  have hcols : (fun t j : Fin (m - 1) => S t.val j.val) =
      (fun t j : Fin (m - 1) => extractionColumns R θ m t.val j) := by
    funext t j
    dsimp [S, removedInverse, extractionColumns]
    rw [ha (j.val + 1) (by omega) (by omega)]
    ring
  have hW' : ∀ n, 0 < windowDet (m - 1) (fun t j => S t j.val) n := by
    intro n
    convert hW n using 1
    unfold windowDet
    congr 1
    ext i j
    dsimp [S, removedInverse, extractionColumns]
    rw [ha (j.val + 1) (by omega) (by omega)]
    ring
  intro n
  change 0 < φ n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hnm : n < m
    · rw [show φ n = initialValue m θ n from canonical_initial m (by omega) F θ n hnm]
      apply prod_pos
      intro t ht
      have ht' := mem_Ico.mp ht
      exact hθ (t + 1) (by omega) (by omega)
    · have hmn : m ≤ n := by omega
      have hφ : ∀ k < n, φ k ≠ 0 := fun k hk => (ih k hk).ne'
      have hrel := quotient_relation n φ hφ
      have hc := canonical_recurrence n m (by omega) F θ
        (fun t ht _ => (hext t ht).ne')
      have hbH : Bandwidth n (m - 1) H :=
        remainder_bandwidth n m (by omega) a φ F (hb n) hrel hφ hc
      have hw := inverse_window_det hH hS (m - 2) (n - m)
        (by simpa only [show n - m + (m - 2) + 2 = n by omega,
          show m - 2 + 1 = m - 1 by omega] using hbH)
      have ht : n - m + (m - 2) + 1 = n - 1 := by omega
      have hd : m - 2 + 1 = m - 1 := by omega
      rw [ht, hd] at hw
      have houter : 0 < H (n - 1) (n - m) := by
        have hp := hW' (n - m + 1)
        rw [hw] at hp
        exact (mul_pos_iff_of_pos_right (hW' (n - m))).mp hp
      have he := weighted_remainder n a φ F hrel (n - m) (m - 1) (by omega)
      have hindex : n - m + (m - 1) = n - 1 := by omega
      rw [hindex] at he
      have hbound : φ (n - 1) * H (n - 1) (n - m) = rhs m F φ n := by
        unfold H remainder
        rw [ite_eq_left (show n - m ≤ n - 1 by omega),
          show n - 1 - (n - m) = m - 1 by omega, he]
        simp only [rhs, show m - 1 + 1 = m by omega]
        apply sum_congr rfl
        intro j hj
        rw [show n - 1 - j = n - (j + 1) by omega]
      have hpos := mul_pos (ih (n - 1) (by omega)) houter
      rw [hbound] at hpos
      have hrec := canonical_recurrence (n + 1) m (by omega) F θ
        (fun t ht _ => (hext t ht).ne') n hmn (by omega)
      change F n (n - m) * φ n = rhs m F φ n at hrec
      rw [← hrec] at hpos
      exact (mul_pos_iff_of_pos_left (hext n hmn)).mp hpos

#print axioms extraction_recurrence_positive
end BTP.SemiInfinite
