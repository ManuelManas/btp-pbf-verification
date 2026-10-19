import OrderedMinors

/-! # Fixed positive bounds from the first factors of a global PBF -/
open Matrix Finset
noncomputable section
namespace BTP.SemiInfinite
open Extraction InverseBounds

def weightedBoundary (V : NatMatrix) (k : ℕ) (α β : ℝ) : Matrix ℕ (Fin (k + 1)) ℝ :=
  fun n j => if j.val = k then α * V n k - β * V n (k + 1) else V n j.val

theorem weightedBoundary_det (V : NatMatrix) (k : ℕ) (α β : ℝ)
    (I : Fin (k + 1) → ℕ) :
    ((weightedBoundary V k α β).submatrix I id).det =
      α * (Matrix.of fun i j : Fin (k + 1) => V (I i) j.val).det -
      β * (Matrix.of fun i j : Fin (k + 1) => V (I i) (nextColumns k j)).det := by
  let A := Matrix.of fun i j : Fin (k + 1) => V (I i) j.val
  let v := fun i : Fin (k + 1) => V (I i) (k + 1)
  have he : (weightedBoundary V k α β).submatrix I id =
      A.updateCol (Fin.last k) (α • (fun i => A i (Fin.last k)) + (-β) • v) := by
    ext i j
    by_cases hj : j = Fin.last k
    · subst j; simp [weightedBoundary, A, v, sub_eq_add_neg]
    · have hv : j.val ≠ k := fun e => hj (Fin.ext e)
      simp [weightedBoundary, Matrix.updateCol_ne hj, hv, A]
  rw [he, Matrix.det_updateCol_add, Matrix.det_updateCol_smul, Matrix.det_updateCol_smul]
  have hself : A.updateCol (Fin.last k) (fun i => A i (Fin.last k)) = A := by
    ext i j; simp
  have hnext : A.updateCol (Fin.last k) v =
      Matrix.of fun i j : Fin (k + 1) => V (I i) (nextColumns k j) := by
    ext i j
    by_cases hj : j = Fin.last k
    · subst j; simp [nextColumns, v]
    · have hv : j.val ≠ k := fun e => hj (Fin.ext e)
      simp [Matrix.updateCol_ne hj, nextColumns, hv, A]
  rw [hself, hnext]
  ring

theorem signed_coordinate_border_nonnegative {k : ℕ} (V : NatMatrix)
    (I : Fin (k + 1) → ℕ) (hI : StrictMono I)
    (hVN : RowNonnegative (fun (n : ℕ) (j : Fin k) => V n j.val)) :
    0 ≤ (Matrix.of fun i j : Fin (k + 1) =>
      if j.val = k then (-1 : ℝ)^k * (if I i = 0 then 1 else 0) else V (I i) j.val).det := by
  let A := Matrix.of fun i j : Fin (k + 1) =>
    if j.val = k then (-1 : ℝ)^k * (if I i = 0 then 1 else 0) else V (I i) j.val
  change 0 ≤ A.det
  rw [Matrix.det_succ_column A (Fin.last k), sum_eq_single (0 : Fin (k + 1))]
  · have hminor : A.submatrix (0 : Fin (k + 1)).succAbove (Fin.last k).succAbove =
        Matrix.of fun i j : Fin k => V (I i.succ) j.val := by
      ext i j
      simp only [Fin.succAbove_zero, Fin.succAbove_last, Matrix.submatrix_apply, A,
        Matrix.of_apply, Fin.val_castSucc, ite_eq_right (show j.val ≠ k by omega)]
    rw [hminor]
    simp only [A, Matrix.of_apply, Fin.val_last, ite_true, Fin.val_zero, Nat.zero_add]
    by_cases hi : I 0 = 0
    · rw [ite_eq_left hi, mul_one, sign_square, one_mul]
      exact hVN (fun i => I i.succ) (hI.comp Fin.strictMono_succ)
    · rw [ite_eq_right hi, mul_zero, mul_zero, zero_mul]
  · intro i _ hi
    have hpos : 0 < I i := by
      have hi0 : (0 : Fin (k + 1)) < i := by change 0 < i.val; exact Nat.pos_of_ne_zero (fun e => hi (Fin.ext e))
      have h := hI hi0
      omega
    simp [A, show I i ≠ 0 by omega]
  · simp

theorem positive_entry_nonnegative {p : ℕ} {b : Entries} (hb : Positive p b)
    (n r : ℕ) (hr : r ≤ n) : 0 ≤ entry b p n r := by
  induction p generalizing n r with
  | zero => simp [entry]; split_ifs <;> norm_num
  | succ p ih =>
    cases r with
    | zero => simp
    | succ r =>
      rw [entry]
      exact add_nonneg (ih (fun j hj t ht => hb j (by omega) t ht) n (r + 1) hr)
        (mul_nonneg (hb p (by omega) n (by omega)).le
          (ih (fun j hj t ht => hb j (by omega) t ht) (n - 1) r (by omega)))

theorem positive_entry_positive {p : ℕ} {b : Entries} (hb : Positive p b)
    (n r : ℕ) (hr : r ≤ n) (hrp : r ≤ p) : 0 < entry b p n r := by
  induction p generalizing n r with
  | zero =>
    have hr0 : r = 0 := by omega
    subst r
    simp
  | succ p ih =>
    cases r with
    | zero => simp
    | succ r =>
      rw [entry]
      exact add_pos_of_nonneg_of_pos
        (positive_entry_nonnegative (fun j hj t ht => hb j (by omega) t ht) n (r + 1) hr)
        (mul_pos (hb p (by omega) n (by omega))
          (ih (fun j hj t ht => hb j (by omega) t ht) (n - 1) r (by omega) (by omega)))

/-- The first column of the banded product gives this exact inverse-column relation. -/
theorem inverse_prefix_column_relation (b : Entries) (k n : ℕ) :
    (∑ j ∈ range (k + 2), (-1 : ℝ)^j * productEntries b (k + 1) j 0 *
      inverseEntries b (k + 1) n j) = if n = 0 then 1 else 0 := by
  let d := n + k + 2
  have he : qProduct d b (k + 1) * checker (lowerProduct d b (k + 1)) = 1 := by
    rw [qProduct_inverse, checker_product]
    apply Matrix.nonsing_inv_mul
    rw [lowerProduct_det]
    exact isUnit_one
  have h := congrArg (fun M : Square d => M ⟨n, by dsimp [d]; omega⟩ ⟨0, by dsimp [d]; omega⟩) he
  rw [Matrix.mul_apply] at h
  simp only [inverseEntries_finite, checker_entry, lowerProduct_entry,
    pow_zero, mul_one, Nat.zero_le, ite_true, Nat.sub_zero, Matrix.one_apply, Fin.ext_iff] at h
  rw [Fin.sum_univ_eq_sum_range
    (fun j : ℕ => inverseEntries b (k + 1) n j * ((-1 : ℝ)^j * entry b (k + 1) j j)) d] at h
  have htrunc : (∑ j ∈ range (k + 2), inverseEntries b (k + 1) n j *
      ((-1 : ℝ)^j * entry b (k + 1) j j)) =
      ∑ j ∈ range d, inverseEntries b (k + 1) n j * ((-1 : ℝ)^j * entry b (k + 1) j j) := by
    apply sum_subset (range_mono (by dsimp [d]; omega))
    intro j _ hj
    have hj' : k + 1 < j := by
      have hn : ¬ j < k + 2 := by simpa only [mem_range] using hj
      omega
    rw [entry_band b (k + 1) j j hj', mul_zero, mul_zero]
  rw [← htrunc] at h
  rw [← h]
  apply sum_congr rfl
  intro j _
  simp only [productEntries, Nat.zero_le, ite_true, Nat.sub_zero]
  ring

theorem inverse_prefix_weighted_nonnegative (b : Entries) (k : ℕ)
    (hb : Positive (k + 1) b) :
    RowNonnegative (weightedBoundary (inverseEntries b (k + 1)) k
      (productEntries b (k + 1) k 0) (productEntries b (k + 1) (k + 1) 0)) := by
  intro I hI
  let V := inverseEntries b (k + 1)
  let h := fun j => productEntries b (k + 1) j 0
  let A := Matrix.of fun i j : Fin (k + 1) => V (I i) j.val
  let v := fun i : Fin (k + 1) => V (I i) (k + 1)
  let e := fun i : Fin (k + 1) => if I i = 0 then (1 : ℝ) else 0
  let c := fun j : Fin (k + 1) => (-1 : ℝ)^j.val * h j.val
  have he : e = (fun i => ∑ j : Fin (k + 1), c j • A i j) +
      ((-1 : ℝ)^(k + 1) * h (k + 1)) • v := by
    funext i
    have heq := inverse_prefix_column_relation b k (I i)
    rw [sum_range_succ] at heq
    dsimp [e, c, A, v, h, V]
    rw [Fin.sum_univ_eq_sum_range
      (fun j : ℕ => ((-1 : ℝ)^j * productEntries b (k + 1) j 0) * inverseEntries b (k + 1) (I i) j)]
    exact heq.symm
  have hd : (A.updateCol (Fin.last k) e).det =
      (-1 : ℝ)^k * h k * A.det +
        ((-1 : ℝ)^(k + 1) * h (k + 1)) * (A.updateCol (Fin.last k) v).det := by
    rw [he, Matrix.det_updateCol_add, Matrix.det_updateCol_sum, Matrix.det_updateCol_smul]
    rfl
  have hborder : 0 ≤ (-1 : ℝ)^k * (A.updateCol (Fin.last k) e).det := by
    rw [← Matrix.det_updateCol_smul]
    have hm : A.updateCol (Fin.last k) ((-1 : ℝ)^k • e) =
        Matrix.of fun i j : Fin (k + 1) =>
          if j.val = k then (-1 : ℝ)^k * (if I i = 0 then 1 else 0) else V (I i) j.val := by
      ext i j
      by_cases hj : j = Fin.last k
      · subst j; simp [e]
      · have hv : j.val ≠ k := fun z => hj (Fin.ext z)
        simp [Matrix.updateCol_ne hj, hv, A]
    rw [hm]
    exact signed_coordinate_border_nonnegative V I hI
      (inverseEntries_ordered_minors (k + 1) b (fun j hj n hn => (hb j hj n hn).le)
        (fun j : Fin k => j.val) (fun i j hij => hij))
  have hnext : A.updateCol (Fin.last k) v =
      Matrix.of fun i j : Fin (k + 1) => V (I i) (nextColumns k j) := by
    ext i j
    by_cases hj : j = Fin.last k
    · subst j; simp [nextColumns, v]
    · have hv : j.val ≠ k := fun z => hj (Fin.ext z)
      simp [Matrix.updateCol_ne hj, hv, nextColumns, A]
  rw [hd, hnext, pow_succ] at hborder
  have hs := sign_square k
  rw [weightedBoundary_det]
  dsimp [V, h, A] at hborder hs ⊢
  nlinarith

#print axioms inverse_prefix_weighted_nonnegative
end BTP.SemiInfinite
