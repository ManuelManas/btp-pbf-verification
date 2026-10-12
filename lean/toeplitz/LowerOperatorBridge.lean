import ToeplitzTail
import PBFMinors

open Matrix Finset Polynomial
noncomputable section
namespace BTP.Toeplitz

def familyOperator (a : Entries) : ℕ → Op
  | 0 => 1
  | p+1 => lower (a p) * familyOperator a p

def LowerLocal (A : Op) : Prop :=
  ∀ (x y : Seq) n, (∀ j, j ≤ n → x j = y j) → A x n = A y n

theorem familyOperator_local (a : Entries) (p : ℕ) : LowerLocal (familyOperator a p) := by
  induction p with
  | zero => intro x y n h; exact h n le_rfl
  | succ p ih =>
    intro x y n h
    cases n with
    | zero =>
      change lower (a p) (familyOperator a p x) 0 = lower (a p) (familyOperator a p y) 0
      rw [lower_zero, lower_zero]
      exact ih x y 0 h
    | succ n =>
      change lower (a p) (familyOperator a p x) (n+1) =
        lower (a p) (familyOperator a p y) (n+1)
      rw [lower_succ, lower_succ, ih x y (n+1) h,
        ih x y n (fun j hj => h j (by omega))]

theorem aeval_backward_local (P : ℝ[X]) : LowerLocal (aeval backward P) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    intro x y n h
    simp only [map_add, LinearMap.add_apply, Pi.add_apply]
    rw [hP x y n h, hQ x y n h]
  | monomial k c =>
    intro x y n h
    rw [aeval_monomial, algebraMap_op]
    change c * ((backward^k) x n) = c * ((backward^k) y n)
    rw [backward_pow_apply, backward_pow_apply]
    by_cases hk : k ≤ n
    · rw [ite_eq_left hk, ite_eq_left hk, h (n-k) (by omega)]
    · rw [ite_eq_right hk, ite_eq_right hk]

/-- Entry equality determines a lower-local operator on all sequences. -/
theorem lowerLocal_ext {A B : Op} (ha : LowerLocal A) (hb : LowerLocal B)
    (he : opMatrix A = opMatrix B) : A = B := by
  ext x n
  let y : Seq := ∑ j : Fin (n+1), x j.val • basis j.val
  have hy : ∀ j, j ≤ n → x j = y j := by
    intro j hj
    dsimp [y]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [sum_eq_single (⟨j, by omega⟩ : Fin (n+1))]
    · simp [basis]
    · intro k _ hk
      have hkj : k.val ≠ j := fun h => hk (Fin.ext h)
      simp [basis, Ne.symm hkj]
    · simp
  rw [ha x y n hy, hb x y n hy]
  dsimp [y]
  simp only [map_sum, LinearMap.map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply sum_congr rfl
  intro j _
  have h := congrArg (fun M : Matrix ℕ ℕ ℝ => M n j.val) he
  change A (basis j.val) n = B (basis j.val) n at h
  rw [h]

theorem productEntries_step (a : Entries) (p n j : ℕ) :
    Extraction.productEntries a (p+1) n j =
      lowerRows (a p) (Extraction.productEntries a p) n j := by
  cases n with
  | zero =>
    simp only [lowerRows, Extraction.productEntries, ite_true, add_zero]
    by_cases hj : j = 0
    · subst j; simp
    · simp [show ¬ j ≤ 0 by omega]
  | succ n =>
    simp only [lowerRows, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
      ite_false, Nat.add_sub_cancel, Extraction.productEntries]
    by_cases hj : j ≤ n
    · rw [ite_eq_left (show j ≤ n+1 by omega), ite_eq_left hj,
        show n+1-j = (n-j)+1 by omega, entry]
      simp [show j ≤ n+1 by omega]
    · by_cases he : j = n+1
      · subst j
        simp [show ¬ n+1 ≤ n by omega]
      · simp [show ¬ j ≤ n+1 by omega, hj]

theorem familyOperator_matrix (a : Entries) (p : ℕ) :
    opMatrix (familyOperator a p) = Extraction.productEntries a p := by
  induction p with
  | zero =>
    rw [familyOperator, opMatrix_one]
    ext i j
    simp only [Extraction.productEntries, entry, Matrix.one_apply]
    by_cases h : i = j
    · subst j; simp
    · by_cases hji : j ≤ i <;> simp [hji, h, show j ≤ i → i-j ≠ 0 by omega]
  | succ p ih =>
    rw [familyOperator, opMatrix_lower_mul, ih]
    ext n j
    exact (productEntries_step a p n j).symm

theorem familyOperator_list (a : Entries) (p : ℕ) :
    familyOperator a p = lowerProduct ((List.range p).reverse.map a) := by
  induction p with
  | zero => simp [familyOperator]
  | succ p ih => simp [familyOperator, List.range_succ, ih]

theorem operator_of_triangular_entries (a : Entries) (m : ℕ) (P : ℝ[X])
    (he : Extraction.productEntries a m = symbolMatrix 0 P) :
    familyOperator a m = aeval backward P := by
  apply lowerLocal_ext (familyOperator_local a m) (aeval_backward_local P)
  rw [familyOperator_matrix, he]
  simpa [symbolOperator] using (symbolOperator_matrix 0 P).symm

#print axioms operator_of_triangular_entries
end BTP.Toeplitz
