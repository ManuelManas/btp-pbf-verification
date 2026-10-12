import Proposition29

/-!+# Proposition 2.15: strictly decreasing inverse-entry bounds

The finite matrices and the factor order are the same as in Lemma24.lean.
Factor indices are reversed: `a j n` is the manuscript's entry in factor
`p-j` and row `n`. No total-positivity or inverse-positivity conclusion is
assumed. All inverse entries and strict inequalities are proved below.
-/

open Finset Matrix
noncomputable section

namespace BTP.InverseBounds

abbrev Square (d : ℕ) := Matrix (Fin d) (Fin d) ℝ

/-- The inverse of a bidiagonal matrix with negative subdiagonal. -/
def chain (d : ℕ) (a : ℕ → ℝ) : Square d :=
  Matrix.of fun i j => if j.val ≤ i.val then ∏ h ∈ Ico j.val i.val, a (h + 1) else 0

@[simp] theorem chain_diag (d : ℕ) (a : ℕ → ℝ) (i : Fin d) : chain d a i i = 1 := by
  simp [chain]

theorem chain_upper {d : ℕ} (a : ℕ → ℝ) (i j : Fin d) (h : i.val < j.val) :
    chain d a i j = 0 := by
  simp only [chain, Matrix.of_apply, ite_eq_right (show ¬ j.val ≤ i.val by omega)]

theorem chain_step {d : ℕ} (a : ℕ → ℝ) (i j : Fin d) (h : j.val < i.val) :
    chain d a i j = a i.val * chain d a ⟨i.val - 1, by omega⟩ j := by
  have hle : j.val ≤ i.val - 1 := by omega
  simp only [chain, Matrix.of_apply, ite_eq_left (Nat.le_of_lt h),
    ite_eq_left hle]
  have hprod := prod_Ico_succ_top hle (fun h => a (h + 1))
  have hi : i.val - 1 + 1 = i.val := by omega
  rw [hi] at hprod
  rw [hprod, mul_comm]

theorem bidiagonal_chain {d : ℕ} (a : ℕ → ℝ) :
    bidiagonal d (fun n => -a n) * chain d a = 1 := by
  ext i j
  by_cases hi : 0 < i.val
  · rw [bidiagonal_mul_pos _ _ _ _ hi]
    by_cases hji : j.val < i.val
    · rw [chain_step a i j hji]
      have hij : i ≠ j := by intro h; subst j; omega
      simp [hij]
    · by_cases hij : i = j
      · subst j
        rw [chain_diag, chain_upper a ⟨i.val - 1, by omega⟩ i (by dsimp; omega)]
        simp
      · have hlt : i.val < j.val := by
          have : i.val ≠ j.val := fun h => hij (Fin.ext h)
          omega
        rw [chain_upper a i j hlt,
          chain_upper a ⟨i.val - 1, by omega⟩ j (by dsimp; omega)]
        simp [hij]
  · have hi0 : i.val = 0 := by omega
    rw [bidiagonal_mul_zero _ _ _ _ hi0]
    by_cases hij : i = j
    · subst j; simp
    · have hlt : i.val < j.val := by
        have : i.val ≠ j.val := fun h => hij (Fin.ext h)
        omega
      simp [chain_upper a i j hlt, hij]

theorem chain_inverse (d : ℕ) (a : ℕ → ℝ) :
    chain d a = (bidiagonal d (fun n => -a n))⁻¹ :=
  (Matrix.inv_eq_right_inv (bidiagonal_chain a)).symm

theorem chain_bidiagonal {d : ℕ} (a : ℕ → ℝ) :
    chain d a * bidiagonal d (fun n => -a n) = 1 := by
  rw [chain_inverse]
  apply Matrix.nonsing_inv_mul
  rw [Extraction.bidiagonal_det]
  exact isUnit_one

def qProduct (d : ℕ) (a : Entries) : ℕ → Square d
  | 0 => 1
  | p + 1 => qProduct d a p * chain d (a p)

theorem qProduct_inverse (d : ℕ) (a : Entries) (p : ℕ) :
    qProduct d a p = (lowerProduct d (fun j n => -a j n) p)⁻¹ := by
  induction p with
  | zero => simp [qProduct, lowerProduct]
  | succ p ih => rw [qProduct, lowerProduct, Matrix.mul_inv_rev, ih, chain_inverse]

theorem qProduct_first (d : ℕ) (a : Entries) (p : ℕ) :
    qProduct d a (p + 1) = chain d (a 0) * qProduct d (fun j n => a (j + 1) n) p := by
  induction p with
  | zero => simp [qProduct]
  | succ p ih => rw [qProduct, ih, qProduct, Matrix.mul_assoc]

theorem first_row_equation (d : ℕ) (a : Entries) (p : ℕ) :
    bidiagonal d (fun n => -a 0 n) * qProduct d a (p + 1) =
      qProduct d (fun j n => a (j + 1) n) p := by
  rw [qProduct_first, ← Matrix.mul_assoc, bidiagonal_chain, Matrix.one_mul]

theorem last_column_equation (d : ℕ) (a : Entries) (p : ℕ) :
    qProduct d a (p + 1) * bidiagonal d (fun n => -a p n) = qProduct d a p := by
  rw [qProduct, Matrix.mul_assoc, chain_bidiagonal, Matrix.mul_one]

/-- Alternating signs on the diagonal. -/
def signs (d : ℕ) : Square d := Matrix.diagonal fun i => (-1 : ℝ) ^ i.val

theorem sign_square (n : ℕ) : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by
  rw [← mul_pow]
  norm_num

theorem signs_square (d : ℕ) : signs d * signs d = 1 := by
  rw [signs, Matrix.diagonal_mul_diagonal]
  simp only [sign_square, Matrix.diagonal_one]

def checker {d : ℕ} (M : Square d) : Square d := signs d * M * signs d

theorem checker_entry {d : ℕ} (M : Square d) (i j : Fin d) :
    checker M i j = (-1 : ℝ) ^ i.val * M i j * (-1 : ℝ) ^ j.val := by
  simp only [checker, signs, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem checker_one (d : ℕ) : checker (1 : Square d) = 1 := by
  rw [checker, Matrix.mul_one, signs_square]

theorem checker_mul {d : ℕ} (M N : Square d) : checker (M * N) = checker M * checker N := by
  unfold checker
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (signs d) (signs d), signs_square, Matrix.one_mul]

theorem checker_twice {d : ℕ} (M : Square d) : checker (checker M) = M := by
  unfold checker
  simp only [← Matrix.mul_assoc]
  rw [signs_square, Matrix.one_mul, Matrix.mul_assoc, signs_square, Matrix.mul_one]

theorem checker_bidiagonal (d : ℕ) (a : ℕ → ℝ) :
    checker (bidiagonal d a) = bidiagonal d (fun n => -a n) := by
  ext i j
  rw [checker_entry]
  by_cases hij : i = j
  · subst j
    simp [bidiagonal, sign_square]
  · by_cases hsub : i.val = j.val + 1
    · simp only [bidiagonal, Matrix.add_apply, Matrix.one_apply, ite_eq_right hij,
        Matrix.of_apply, ite_eq_left hsub, zero_add]
      rw [hsub, pow_succ]
      calc
        _ = -a (j.val + 1) * ((-1 : ℝ) ^ j.val * (-1 : ℝ) ^ j.val) := by ring
        _ = _ := by rw [sign_square, mul_one]
    · simp [bidiagonal, hij, hsub]

theorem checker_product (d : ℕ) (a : Entries) (p : ℕ) :
    checker (lowerProduct d a p) = lowerProduct d (fun j n => -a j n) p := by
  induction p with
  | zero => exact checker_one d
  | succ p ih => rw [lowerProduct, checker_mul, checker_bidiagonal, ih, lowerProduct]

theorem lowerProduct_det (d : ℕ) (a : Entries) (p : ℕ) : (lowerProduct d a p).det = 1 := by
  induction p with
  | zero => simp [lowerProduct]
  | succ p ih => rw [lowerProduct, Matrix.det_mul, Extraction.bidiagonal_det, ih, one_mul]

theorem checker_inverse {d : ℕ} (M : Square d) (h : IsUnit M.det) :
    checker (M⁻¹) = (checker M)⁻¹ := by
  symm
  apply Matrix.inv_eq_right_inv
  rw [← checker_mul, Matrix.mul_nonsing_inv M h, checker_one]

/-- This is exactly J G⁻¹ J, not a separately postulated positive matrix. -/
theorem qProduct_signed_inverse (d : ℕ) (a : Entries) (p : ℕ) :
    qProduct d a p = checker ((lowerProduct d a p)⁻¹) := by
  rw [checker_inverse _ (by rw [lowerProduct_det]; exact isUnit_one),
    checker_product, qProduct_inverse]

theorem checker_lower_entry {d : ℕ} (M : Square d) (i j : Fin d) (h : j.val ≤ i.val) :
    checker M i j = (-1 : ℝ) ^ (i.val - j.val) * M i j := by
  rw [checker_entry]
  have hi : i.val = (i.val - j.val) + j.val := by omega
  conv_lhs => arg 1; arg 1; rw [hi, pow_add]
  have hs := sign_square j.val
  calc
    _ = (-1 : ℝ) ^ (i.val - j.val) * M i j *
        ((-1 : ℝ) ^ j.val * (-1 : ℝ) ^ j.val) := by ring
    _ = _ := by rw [hs, mul_one]

def Nonnegative {d : ℕ} (M : Square d) : Prop := ∀ i j, 0 ≤ M i j

theorem nonnegative_one (d : ℕ) : Nonnegative (1 : Square d) := by
  intro i j
  simp only [Matrix.one_apply]
  split_ifs <;> norm_num

theorem nonnegative_mul {d : ℕ} {M N : Square d}
    (hM : Nonnegative M) (hN : Nonnegative N) : Nonnegative (M * N) := by
  intro i j
  rw [Matrix.mul_apply]
  exact sum_nonneg fun k _ => mul_nonneg (hM i k) (hN k j)

theorem mul_entry_pos {d : ℕ} {M N : Square d}
    (hM : Nonnegative M) (hN : Nonnegative N) (i j k : Fin d)
    (hMk : 0 < M i k) (hNk : 0 < N k j) : 0 < (M * N) i j := by
  exact sum_pos' (fun l _ => mul_nonneg (hM i l) (hN l j))
    ⟨k, mem_univ k, mul_pos hMk hNk⟩

theorem chain_nonnegative {d : ℕ} (a : ℕ → ℝ)
    (ha : ∀ n, 0 < n → n < d → 0 ≤ a n) : Nonnegative (chain d a) := by
  intro i j
  simp only [chain, Matrix.of_apply]
  split_ifs
  · apply prod_nonneg
    intro k hk
    have hk' := mem_Ico.mp hk
    exact ha (k + 1) (by omega) (by omega)
  · exact le_rfl

theorem chain_pos {d : ℕ} (a : ℕ → ℝ) (i j : Fin d) (hji : j.val ≤ i.val)
    (ha : ∀ n, j.val < n → n ≤ i.val → 0 < a n) : 0 < chain d a i j := by
  simp only [chain, Matrix.of_apply, ite_eq_left hji]
  apply prod_pos
  intro k hk
  have hk' := mem_Ico.mp hk
  exact ha (k + 1) (by omega) (by omega)

theorem qProduct_nonnegative {d : ℕ} (a : Entries) (p : ℕ)
    (ha : ∀ j < p, ∀ n, 0 < n → n < d → 0 ≤ a j n) : Nonnegative (qProduct d a p) := by
  induction p with
  | zero => exact nonnegative_one d
  | succ p ih =>
    exact nonnegative_mul (ih (fun j hj => ha j (by omega)))
      (chain_nonnegative (a p) (ha p (by omega)))

theorem qProduct_diag_pos {d : ℕ} (a : Entries) (p : ℕ)
    (ha : ∀ j < p, ∀ n, 0 < n → n < d → 0 ≤ a j n) (i : Fin d) :
    0 < qProduct d a p i i := by
  induction p with
  | zero => simp [qProduct]
  | succ p ih =>
    have hp := fun j (hj : j < p) => ha j (by omega : j < p + 1)
    exact mul_entry_pos (qProduct_nonnegative a p hp)
      (chain_nonnegative (a p) (ha p (by omega))) i i i (ih hp) (by simp)

/-- A positive chain in the rightmost original factor stays positive in the inverse product. -/
theorem qProduct_chain_pos {d : ℕ} (a : Entries) (p : ℕ)
    (ha : ∀ j < p + 1, ∀ n, 0 < n → n < d → 0 ≤ a j n)
    (i j : Fin d) (hji : j.val ≤ i.val)
    (hfirst : ∀ n, j.val < n → n ≤ i.val → 0 < a 0 n) :
    0 < qProduct d a (p + 1) i j := by
  rw [qProduct_first]
  have hs : ∀ k < p, ∀ n, 0 < n → n < d → 0 ≤ a (k + 1) n :=
    fun k hk => ha (k + 1) (by omega)
  exact mul_entry_pos (chain_nonnegative (a 0) (ha 0 (by omega)))
    (qProduct_nonnegative _ p hs) i j j (chain_pos (a 0) i j hji hfirst)
    (qProduct_diag_pos _ p hs j)

def FixesZero {d : ℕ} (M : Square d) : Prop :=
  ∀ i j : Fin d, j.val = 0 → M i j = (1 : Square d) i j

theorem chain_fixes_zero {d : ℕ} (a : ℕ → ℝ) (ha : a 1 = 0) :
    FixesZero (chain d a) := by
  intro i j hj
  by_cases hij : i = j
  · subst j; simp
  · have hi : 0 < i.val := by
      have : i.val ≠ j.val := fun h => hij (Fin.ext h)
      omega
    simp only [chain, Matrix.of_apply, ite_eq_left (show j.val ≤ i.val by omega),
      Matrix.one_apply, ite_eq_right hij]
    exact prod_eq_zero (show 0 ∈ Ico j.val i.val by simp [hj, hi]) (by simpa using ha)

theorem fixes_zero_mul {d : ℕ} {M N : Square d} (hM : FixesZero M) (hN : FixesZero N) :
    FixesZero (M * N) := by
  intro i j hj
  calc
    (M * N) i j = (M * (1 : Square d)) i j := by
      simp only [Matrix.mul_apply]
      apply sum_congr rfl
      intro k _
      rw [hN k j hj]
    _ = (1 : Square d) i j := by rw [Matrix.mul_one, hM i j hj]

theorem qProduct_fixes_zero {d : ℕ} (a : Entries) (p : ℕ)
    (ha : ∀ j < p, a j 1 = 0) : FixesZero (qProduct d a p) := by
  induction p with
  | zero => intro i j _; rfl
  | succ p ih =>
    exact fixes_zero_mul (ih (fun j hj => ha j (by omega)))
      (chain_fixes_zero (a p) (ha p (by omega)))

/-- Precisely the initial zero pattern and positive entries of the lower Metelmann factors. -/
def Metelmann (d p : ℕ) (a : Entries) : Prop :=
  (∀ j < p, ∀ n, 0 < n → n ≤ j → a j n = 0) ∧
  (∀ j < p, ∀ n < d, j < n → 0 < a j n)

theorem Metelmann.nonnegative {d p : ℕ} {a : Entries} (h : Metelmann d p a) :
    ∀ j < p, ∀ n, 0 < n → n < d → 0 ≤ a j n := by
  intro j hj n hn hnd
  by_cases hnj : n ≤ j
  · rw [h.1 j hj n hn hnj]
  · exact le_of_lt (h.2 j hj n hnd (by omega))

theorem metelmann_inverse_pos {d p : ℕ} (a : Entries) (hp : 1 ≤ p)
    (ha : Metelmann d p a) (i j : Fin d) (hji : j.val ≤ i.val) :
    0 < qProduct d a p i j := by
  have heq : p - 1 + 1 = p := by omega
  have hnn := ha.nonnegative
  rw [← heq]
  apply qProduct_chain_pos a (p - 1) (by simpa only [heq] using hnn) i j hji
  intro n hn hni
  exact ha.2 0 (by omega) n (by omega) (by omega)

def tail (d : ℕ) (a : Entries) (p : ℕ) : Square d :=
  qProduct d (fun j n => a (j + 1) n) (p - 1)

theorem metelmann_tail_fixes_zero {d p : ℕ} (a : Entries) (ha : Metelmann d p a) :
    FixesZero (tail d a p) := by
  apply qProduct_fixes_zero
  intro j hj
  exact ha.1 (j + 1) (by omega) 1 (by omega) (by omega)

theorem metelmann_tail_column_one {d p : ℕ} (a : Entries) (hp : 2 ≤ p)
    (ha : Metelmann d p a) (i j : Fin d) (hj : j.val = 1) (hi : 1 ≤ i.val) :
    0 < tail d a p i j := by
  unfold tail
  have heq : p - 2 + 1 = p - 1 := by omega
  rw [← heq]
  refine qProduct_chain_pos _ (p - 2) ?_ i j (by omega) ?_
  · intro k hk n hn hnd
    exact ha.nonnegative (k + 1) (by omega) n hn hnd
  · intro n hn hni
    exact ha.2 1 (by omega) n (by omega) (by omega)

/-- Exact identity replacing the Cauchy--Binet step of the printed proof. -/
theorem adjacent_minor_identity {d p : ℕ} (a : Entries) (hp : 1 ≤ p)
    (ha : Metelmann d p a) (z o n s : Fin d)
    (hz : z.val = 0) (_ho : o.val = 1) (hs : s.val = n.val + 1) :
    qProduct d a p n z * qProduct d a p s o -
      qProduct d a p n o * qProduct d a p s z =
        qProduct d a p n z * tail d a p s o := by
  have hrows : bidiagonal d (fun k => -a 0 k) * qProduct d a p = tail d a p := by
    have h := first_row_equation d a (p - 1)
    simpa only [show p - 1 + 1 = p by omega, tail] using h
  have hspos : 0 < s.val := by omega
  have hprev : (⟨s.val - 1, by omega⟩ : Fin d) = n := by
    apply Fin.ext
    change s.val - 1 = n.val
    omega
  have h0 := congrArg (fun M : Square d => M s z) hrows
  have h1 := congrArg (fun M : Square d => M s o) hrows
  rw [bidiagonal_mul_pos _ _ _ _ hspos, hprev] at h0 h1
  have hsz : s ≠ z := by intro h; subst z; omega
  rw [metelmann_tail_fixes_zero a ha s z hz, Matrix.one_apply, ite_eq_right hsz] at h0
  have e0 : qProduct d a p s z = a 0 s.val * qProduct d a p n z := by linarith
  have e1 : qProduct d a p s o = tail d a p s o + a 0 s.val * qProduct d a p n o := by
    linarith
  rw [e0, e1]
  ring

theorem adjacent_minor_pos {d p : ℕ} (a : Entries) (hp : 2 ≤ p)
    (ha : Metelmann d p a) (z o n s : Fin d)
    (hz : z.val = 0) (ho : o.val = 1) (hs : s.val = n.val + 1) :
    0 < qProduct d a p n z * qProduct d a p s o -
      qProduct d a p n o * qProduct d a p s z := by
  rw [adjacent_minor_identity a (by omega) ha z o n s hz ho hs]
  exact mul_pos (metelmann_inverse_pos a (by omega) ha n z (by omega))
    (metelmann_tail_column_one a hp ha s o ho (by omega))

/-- The paper's inverse-entry ratio. The proof `hd` just makes column 1 a valid index. -/
def kappa {d : ℕ} (hd : 1 < d) (a : Entries) (p : ℕ) (n : Fin d) : ℝ :=
  qProduct d a p n ⟨0, by omega⟩ / qProduct d a p n ⟨1, hd⟩

theorem kappa_pos {d p : ℕ} (hd : 1 < d) (a : Entries) (hp : 1 ≤ p)
    (ha : Metelmann d p a) (n : Fin d) (hn : 1 ≤ n.val) : 0 < kappa hd a p n := by
  exact div_pos (metelmann_inverse_pos a hp ha n ⟨0, by omega⟩ (by dsimp; omega))
    (metelmann_inverse_pos a hp ha n ⟨1, hd⟩ hn)

theorem kappa_strictly_decreasing {d p : ℕ} (hd : 1 < d) (a : Entries) (hp : 2 ≤ p)
    (ha : Metelmann d p a) (n s : Fin d) (hn : 1 ≤ n.val) (hs : s.val = n.val + 1) :
    kappa hd a p s < kappa hd a p n ∧ 0 < kappa hd a p s := by
  refine ⟨?_, kappa_pos hd a (by omega) ha s (by omega)⟩
  unfold kappa
  apply (div_lt_div_iff₀
    (metelmann_inverse_pos a (by omega) ha s ⟨1, hd⟩ (by dsimp; omega))
    (metelmann_inverse_pos a (by omega) ha n ⟨1, hd⟩ hn)).mpr
  have h := adjacent_minor_pos a hp ha ⟨0, by omega⟩ ⟨1, hd⟩ n s rfl rfl hs
  nlinarith

theorem mul_bidiagonal_column_zero {d : ℕ} (a : ℕ → ℝ) (M : Square d)
    (i z o : Fin d) (hz : z.val = 0) (ho : o.val = 1) :
    (M * bidiagonal d a) i z = M i z + M i o * a 1 := by
  rw [bidiagonal, Matrix.mul_add, Matrix.mul_one]
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply]
  congr 1
  rw [sum_eq_single o]
  · rw [ite_eq_left (show o.val = z.val + 1 by omega), ho]
  · intro k _ hk
    have hne : k.val ≠ z.val + 1 := by
      intro h
      apply hk
      apply Fin.ext
      omega
    rw [ite_eq_right hne, mul_zero]
  · simp

/-- Positive entries in an arbitrary bidiagonal refactorization. -/
def PositiveFactors (d p : ℕ) (b : Entries) : Prop :=
  ∀ j < p, ∀ n, 0 < n → n < d → 0 < b j n

theorem positive_inverse_entries {d p : ℕ} (b : Entries) (hp : 1 ≤ p)
    (hb : PositiveFactors d p b) (i j : Fin d) (hji : j.val ≤ i.val) :
    0 < qProduct d b p i j := by
  have heq : p - 1 + 1 = p := by omega
  rw [← heq]
  refine qProduct_chain_pos b (p - 1) ?_ i j hji ?_
  · intro k hk n hn hnd
    exact le_of_lt (hb k (by omega) n hn hnd)
  · intro n hn hni
    exact hb 0 (by omega) n (by omega) (by omega)

/-- Removing the leftmost positive factor gives the strict inequality in every row. -/
theorem positive_refactorization_bound {d p : ℕ} (hd : 1 < d) (a b : Entries) (hp : 2 ≤ p)
    (ha : Metelmann d p a) (hb : PositiveFactors d p b)
    (heq : lowerProduct d b p = lowerProduct d a p) (n : Fin d) (hn : 1 ≤ n.val) :
    0 < b (p - 1) 1 ∧ b (p - 1) 1 < kappa hd a p n := by
  have hQ : qProduct d b p = qProduct d a p := by
    rw [qProduct_signed_inverse, qProduct_signed_inverse, heq]
  let z : Fin d := ⟨0, by omega⟩
  let o : Fin d := ⟨1, hd⟩
  have hcol : qProduct d a p * bidiagonal d (fun k => -b (p - 1) k) =
      qProduct d b (p - 1) := by
    have h := last_column_equation d b (p - 1)
    rw [show p - 1 + 1 = p by omega, hQ] at h
    exact h
  have hentry := congrArg (fun M : Square d => M n z) hcol
  rw [mul_bidiagonal_column_zero _ _ n z o rfl rfl] at hentry
  have hrem : 0 < qProduct d b (p - 1) n z :=
    positive_inverse_entries b (by omega) (fun j hj => hb j (by omega)) n z (by dsimp [z]; omega)
  have hden : 0 < qProduct d a p n o := metelmann_inverse_pos a (by omega) ha n o hn
  refine ⟨hb (p - 1) (by omega) 1 (by omega) hd, ?_⟩
  apply (lt_div_iff₀ hden).mpr
  change b (p - 1) 1 * qProduct d a p n o < qProduct d a p n z
  nlinarith

/-- The exact entry notation used in the statement of Proposition 2.15. -/
def inverseEntry {d : ℕ} (G : Square d) (i j : Fin d) : ℝ :=
  (-1 : ℝ) ^ (i.val - j.val) * G⁻¹ i j

theorem qProduct_entry_eq {d : ℕ} (a : Entries) (p : ℕ) (i j : Fin d) (hji : j.val ≤ i.val) :
    qProduct d a p i j = inverseEntry (lowerProduct d a p) i j := by
  rw [qProduct_signed_inverse, checker_lower_entry _ i j hji]
  rfl

def inverseRatio {d : ℕ} (hd : 1 < d) (G : Square d) (n : Fin d) : ℝ :=
  inverseEntry G n ⟨0, by omega⟩ / inverseEntry G n ⟨1, hd⟩

theorem kappa_eq_inverseRatio {d : ℕ} (hd : 1 < d) (a : Entries) (p : ℕ)
    (n : Fin d) (hn : 1 ≤ n.val) : kappa hd a p n = inverseRatio hd (lowerProduct d a p) n := by
  unfold kappa inverseRatio
  rw [qProduct_entry_eq a p n ⟨0, by omega⟩ (by dsimp; omega),
    qProduct_entry_eq a p n ⟨1, hd⟩ hn]

/-- Proposition 2.15 in full, with the actual finite matrix inverse.

The three conclusions are positivity of the two entries, strict decrease
of adjacent ratios, and the bound for every positive refactorization of G.
The last coefficient `b (p-1) 1` is the entry [L₁]₁₀ in the paper.
-/
theorem proposition_2_15 {d p : ℕ} (a : Entries) (hp : 2 ≤ p) (hpd : p < d)
    (ha : Metelmann d p a) :
    (∀ n : Fin d, 1 ≤ n.val →
      0 < inverseEntry (lowerProduct d a p) n ⟨0, by omega⟩ ∧
      0 < inverseEntry (lowerProduct d a p) n ⟨1, by omega⟩) ∧
    (∀ n s : Fin d, 1 ≤ n.val → s.val = n.val + 1 →
      inverseRatio (by omega) (lowerProduct d a p) s <
        inverseRatio (by omega) (lowerProduct d a p) n ∧
      0 < inverseRatio (by omega) (lowerProduct d a p) s) ∧
    (∀ b : Entries, PositiveFactors d p b → lowerProduct d b p = lowerProduct d a p →
      0 < b (p - 1) 1 ∧
      b (p - 1) 1 < inverseRatio (by omega) (lowerProduct d a p) ⟨d - 1, by omega⟩) := by
  have hd : 1 < d := by omega
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    constructor
    · rw [← qProduct_entry_eq a p n ⟨0, by omega⟩ (by dsimp; omega)]
      exact metelmann_inverse_pos a (by omega) ha n _ (by dsimp; omega)
    · rw [← qProduct_entry_eq a p n ⟨1, hd⟩ hn]
      exact metelmann_inverse_pos a (by omega) ha n _ hn
  · intro n s hn hs
    have h := kappa_strictly_decreasing hd a hp ha n s hn hs
    rw [kappa_eq_inverseRatio hd a p n hn,
      kappa_eq_inverseRatio hd a p s (by omega)] at h
    exact h
  · intro b hb heq
    have h := positive_refactorization_bound hd a b hp ha hb heq ⟨d - 1, by omega⟩ (by dsimp; omega)
    rw [kappa_eq_inverseRatio hd a p ⟨d - 1, by omega⟩ (by dsimp; omega)] at h
    exact h

/-- Extract coordinates from an arbitrary matrix; only rows 1 through d-1 matter. -/
def subdiagonalCoordinates {d : ℕ} (M : Square d) (n : ℕ) : ℝ :=
  if hn : 0 < n ∧ n < d then M ⟨n, hn.2⟩ ⟨n - 1, by omega⟩ else 0

theorem subdiagonalCoordinates_entry {d : ℕ} (M : Square d) (i j : Fin d)
    (hij : i.val = j.val + 1) : subdiagonalCoordinates M i.val = M i j := by
  unfold subdiagonalCoordinates
  rw [dite_eq_left (show 0 < i.val ∧ i.val < d by constructor <;> omega)]
  congr 1
  apply Fin.ext
  change i.val - 1 = j.val
  omega

/-- No unit lower bidiagonal matrices are lost by the coordinate representation. -/
theorem unit_bidiagonal_representation {d : ℕ} (M : Square d) (hM : UnitLowerBidiagonal M) :
    bidiagonal d (subdiagonalCoordinates M) = M := by
  ext i j
  by_cases hij : i = j
  · subst j
    rw [(bidiagonal_unit d _).1 i, hM.1 i]
  · by_cases hsub : i.val = j.val + 1
    · rw [bidiagonal_subdiagonal _ i j hsub, subdiagonalCoordinates_entry M i j hsub]
    · rw [(bidiagonal_unit d _).2 i j hij hsub, hM.2 i j hij hsub]

def factorProduct (d : ℕ) (F : ℕ → Square d) : ℕ → Square d
  | 0 => 1
  | p + 1 => F p * factorProduct d F p

theorem factorProduct_coordinates {d : ℕ} (F : ℕ → Square d) (p : ℕ)
    (hF : ∀ j < p, UnitLowerBidiagonal (F j)) :
    factorProduct d F p = lowerProduct d (fun j => subdiagonalCoordinates (F j)) p := by
  induction p with
  | zero => rfl
  | succ p ih =>
    rw [factorProduct, lowerProduct, unit_bidiagonal_representation (F p) (hF p (by omega)),
      ih (fun j hj => hF j (by omega))]

/-- The bound with arbitrary matrix factors, rather than prescribed coordinate arrays.
`F (p-1)` is the leftmost factor and `F 0` the rightmost.
-/
theorem arbitrary_positive_refactorization_bound {d p : ℕ} (a : Entries)
    (hp : 2 ≤ p) (hpd : p < d) (ha : Metelmann d p a) (F : ℕ → Square d)
    (hF : ∀ j < p, PositiveLowerBidiagonal (F j))
    (heq : factorProduct d F p = lowerProduct d a p) :
    0 < F (p - 1) ⟨1, by omega⟩ ⟨0, by omega⟩ ∧
    F (p - 1) ⟨1, by omega⟩ ⟨0, by omega⟩ <
      inverseRatio (by omega) (lowerProduct d a p) ⟨d - 1, by omega⟩ := by
  let b : Entries := fun j => subdiagonalCoordinates (F j)
  have hb : PositiveFactors d p b := by
    intro j hj n hn hnd
    change subdiagonalCoordinates (F j) n > 0
    rw [subdiagonalCoordinates, dite_eq_left ⟨hn, hnd⟩]
    apply (hF j hj).2
    dsimp
    omega
  have heqb : lowerProduct d b p = lowerProduct d a p := by
    rw [← factorProduct_coordinates F p (fun j hj => (hF j hj).1)]
    exact heq
  have h := (proposition_2_15 a hp hpd ha).2.2 b hb heqb
  change 0 < subdiagonalCoordinates (F (p - 1)) 1 ∧
    subdiagonalCoordinates (F (p - 1)) 1 < _ at h
  rw [subdiagonalCoordinates_entry (F (p - 1)) ⟨1, by omega⟩ ⟨0, by omega⟩ rfl] at h
  exact h

#print axioms qProduct_signed_inverse
#print axioms adjacent_minor_identity
#print axioms positive_refactorization_bound
#print axioms proposition_2_15
#print axioms arbitrary_positive_refactorization_bound

end BTP.InverseBounds
