import InverseSections

/-! # Consecutive inverse minors in arbitrary bandwidth

The elimination below is on actual inverse entries. At stage l the first
l rows have reached their final form; the remaining rows come from the
inverse of the remaining Metelmann factors. The determinant is unchanged.
-/

open Matrix Finset
noncomputable section
namespace BTP.SemiInfinite
open InverseBounds

/-- If every factor fixes e_j, so does the product of their signed inverses. -/
theorem inverseEntries_fixed_column (a : Entries) (p j : ℕ)
    (hz : ∀ i < p, a i (j + 1) = 0) (n : ℕ) :
    inverseEntries a p n j = if n = j then 1 else 0 := by
  induction p generalizing a n with
  | zero => rfl
  | succ p ih =>
    induction n with
    | zero => simp
    | succ n ihn =>
      by_cases hnj : n + 1 = j
      · subst j; rw [inverseEntries_diagonal]; simp
      · rw [inverseEntries_succ, ih (fun i m => a (i + 1) m)
          (fun i hi => hz (i + 1) (by omega)), ihn, ite_eq_right hnj]
        by_cases hn : n = j
        · subst n; rw [hz 0 (by omega)]; simp
        · simp [hn]

/-- Drop the first l factors in the inverse product (numbered from the right). -/
def qTail (a : Entries) (p l n j : ℕ) : ℝ :=
  inverseEntries (fun i t => a (i + l) t) (p - l) n j

@[simp] theorem qTail_zero (a : Entries) (p n j : ℕ) :
    qTail a p 0 n j = inverseEntries a p n j := by simp [qTail]

theorem qTail_succ_row (a : Entries) (p l n j : ℕ) (hl : l < p) :
    qTail a p l (n + 1) j = qTail a p (l + 1) (n + 1) j +
      a l (n + 1) * qTail a p l n j := by
  unfold qTail
  have h : p - l = (p - (l + 1)) + 1 := by omega
  rw [h, inverseEntries_succ]
  simp only [Nat.zero_add, Nat.add_assoc, Nat.add_comm 1 l]

theorem qTail_column_before {p : ℕ} {a : Entries} (ha : SemiInfinite.Metelmann p a)
    {l j n : ℕ} (hjl : j < l) (hln : l ≤ n) : qTail a p l n j = 0 := by
  unfold qTail
  rw [inverseEntries_fixed_column]
  · exact ite_eq_right (by omega)
  · intro i hi
    exact ha.1 (i + l) (by omega) (j + 1) (by omega) (by omega)

theorem cumulative_succ (a : Entries) (l n : ℕ) (h : l ≤ n) :
    cumulative a l (n + 1) = cumulative a l n * a l (n + 1) := by
  exact prod_Ico_succ_top h (fun t => a l (t + 1))

theorem qTail_diagonal_column {p : ℕ} {a : Entries} (ha : SemiInfinite.Metelmann p a)
    {l : ℕ} (hl : l < p) {n : ℕ} (hln : l ≤ n) :
    qTail a p l n l = cumulative a l n := by
  induction n, hln using Nat.le_induction with
  | base => simp [qTail, inverseEntries_diagonal, cumulative]
  | succ n hn ih =>
    rw [qTail_succ_row _ _ _ _ _ hl, qTail_column_before ha (by omega) (by omega), ih,
      cumulative_succ _ _ _ hn]
    ring

/-- Arbitrary columns; they need not be increasing for the algebraic identity. -/
def consecutiveMinor (a : Entries) (p k n : ℕ) (c : Fin k → ℕ) : ℝ :=
  (Matrix.of fun i j : Fin k => inverseEntries a p (n + i.val) (c j)).det

def eliminationStage (a : Entries) (p k n : ℕ) (c : Fin k → ℕ) (l : ℕ) :
    Matrix (Fin k) (Fin k) ℝ :=
  fun i j => qTail a p (min i.val l) (n + i.val) (c j)

theorem elimination_step (a : Entries) (p k n : ℕ) (c : Fin k → ℕ)
    {l : ℕ} (hl : l < p) :
    (eliminationStage a p k n c l).det =
      (eliminationStage a p k n c (l + 1)).det := by
  cases k with
  | zero => simp
  | succ k =>
    apply Matrix.det_eq_of_forall_row_eq_smul_add_pred
      (fun i : Fin k => if l ≤ i.val then a l (n + i.val + 1) else 0)
    · intro j; simp [eliminationStage]
    · intro i j
      change qTail a p (min (i.val + 1) l) (n + (i.val + 1)) (c j) =
        qTail a p (min (i.val + 1) (l + 1)) (n + (i.val + 1)) (c j) +
        (if l ≤ i.val then a l (n + i.val + 1) else 0) *
          qTail a p (min i.val l) (n + i.val) (c j)
      by_cases h : l ≤ i.val
      · rw [Nat.min_eq_right (show l ≤ i.val + 1 by omega),
          Nat.min_eq_right (show l + 1 ≤ i.val + 1 by omega), Nat.min_eq_right h, ite_eq_left h]
        simpa only [Nat.add_assoc] using qTail_succ_row a p l (n + i.val) (c j) hl
      · rw [Nat.min_eq_left (show i.val + 1 ≤ l by omega),
          Nat.min_eq_left (show i.val + 1 ≤ l + 1 by omega), ite_eq_right h, zero_mul, add_zero]

theorem elimination_all (a : Entries) (p k n : ℕ) (c : Fin k → ℕ)
    {l : ℕ} (hl : l ≤ p) :
    consecutiveMinor a p k n c = (eliminationStage a p k n c l).det := by
  induction l with
  | zero =>
    apply congrArg Matrix.det
    ext i j
    simp [eliminationStage]
  | succ l ih => exact (ih (by omega)).trans (elimination_step a p k n c (by omega))

/-- The leading inverse minor is an explicit positive product. -/
theorem leading_minor_formula {p k : ℕ} {a : Entries}
    (ha : SemiInfinite.Metelmann p a) (hk : k ≤ p) (n : ℕ) :
    consecutiveMinor a p k n (fun j => j.val) =
      ∏ i : Fin k, cumulative a i.val (n + i.val) := by
  rw [elimination_all a p k n (fun j => j.val) hk]
  have htri : (eliminationStage a p k n (fun j => j.val) k).IsUpperTriangular := by
    intro i j hij
    change qTail a p (min i.val k) (n + i.val) j.val = 0
    rw [Nat.min_eq_left (Nat.le_of_lt i.isLt)]
    exact qTail_column_before ha hij (by omega)
  rw [Matrix.det_of_isUpperTriangular htri]
  apply prod_congr rfl
  intro i _
  change qTail a p (min i.val k) (n + i.val) i.val = _
  rw [Nat.min_eq_left (Nat.le_of_lt i.isLt)]
  exact qTail_diagonal_column ha (by omega) (by omega)

theorem leading_minor_pos {p k : ℕ} {a : Entries}
    (ha : SemiInfinite.Metelmann p a) (hk : k ≤ p) (n : ℕ) :
    0 < consecutiveMinor a p k n (fun j => j.val) := by
  rw [leading_minor_formula ha hk]
  exact prod_pos (fun i _ => cumulative_pos ha (by omega) _)

/-- Normalized tail columns, appearing after the row eliminations. -/
def normalizedTail (a : Entries) (p l n j : ℕ) : ℝ :=
  qTail a p l n j / cumulative a l n

/-- The normalized-minor identity for EVERY choice of columns. -/
theorem normalized_minor_identity {p k : ℕ} {a : Entries}
    (ha : SemiInfinite.Metelmann p a) (hk : k ≤ p) (n : ℕ) (c : Fin k → ℕ) :
    consecutiveMinor a p k n c / consecutiveMinor a p k n (fun j => j.val) =
      (Matrix.of fun i j : Fin k => normalizedTail a p i.val (n + i.val) (c j)).det := by
  have hmat : eliminationStage a p k n c k =
      Matrix.of (fun i j : Fin k => cumulative a i.val (n + i.val) *
        normalizedTail a p i.val (n + i.val) (c j)) := by
    ext i j
    simp only [eliminationStage, Matrix.of_apply, Nat.min_eq_left (Nat.le_of_lt i.isLt), normalizedTail]
    field_simp [(cumulative_pos ha (show i.val < p by omega) _).ne']
  have hs := Matrix.det_mul_column (fun i : Fin k => cumulative a i.val (n + i.val))
    (Matrix.of fun i j : Fin k => normalizedTail a p i.val (n + i.val) (c j))
  rw [elimination_all a p k n c hk, hmat, leading_minor_formula ha hk]
  simp only [Matrix.of_apply] at hs
  rw [hs]
  exact mul_div_cancel_left₀ _ (ne_of_gt (prod_pos (fun i _ => cumulative_pos ha (by omega) _)))

#print axioms leading_minor_formula
#print axioms normalized_minor_identity
end BTP.SemiInfinite
