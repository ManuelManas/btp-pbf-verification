import FactorReordering
import Mathlib.Algebra.Polynomial.AlgebraMap

/-! The polynomial symbol and the actual Toeplitz entries. The equality is
proved at the semi-infinite left boundary as well as in the constant tail. -/

open Polynomial
noncomputable section
namespace BTP.Toeplitz

def forward : Op where
  toFun x n := x (n+1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def backward : Op where
  toFun x n := if n = 0 then 0 else x (n-1)
  map_add' x y := by ext n; by_cases hn : n = 0 <;> simp [hn]
  map_smul' c x := by ext n; by_cases hn : n = 0 <;> simp [hn]

@[simp] theorem forward_apply (x : Seq) (n : ℕ) : forward x n = x (n+1) := rfl
@[simp] theorem backward_zero (x : Seq) : backward x 0 = 0 := by simp [backward]
@[simp] theorem backward_succ (x : Seq) (n : ℕ) : backward x (n+1) = x n := by simp [backward]

theorem forward_backward : forward * backward = 1 := by
  ext x n
  change backward x (n+1) = x n
  simp

theorem constant_lower (β : ℝ) : lower (fun _ => β) = 1 + β • backward := by
  ext x n
  cases n <;> simp [lower, backward]

theorem constant_upper (β : ℝ) : upper (fun _ => β) = forward + β • (1 : Op) := by
  ext x n
  change β * x n + x (n+1) = x (n+1) + β * x n
  ring

theorem algebraMap_op (c : ℝ) : algebraMap ℝ Op c = diagonal (fun _ => c) := by
  ext x n
  rfl

theorem aeval_linear_factor (β : ℝ) :
    aeval backward (1 + C β * X) = lower (fun _ => β) := by
  rw [map_add, map_one, map_mul, aeval_C, aeval_X, algebraMap_op, constant_lower]
  congr 1

/-- The finite product in the root parametrization, without the positive scale. -/
def rootPolynomial (bs : List ℝ) : ℝ[X] := (bs.map (fun β => 1 + C β * X)).prod

@[simp] theorem rootPolynomial_nil : rootPolynomial [] = 1 := rfl
@[simp] theorem rootPolynomial_cons (β : ℝ) (bs : List ℝ) :
    rootPolynomial (β :: bs) = (1 + C β * X) * rootPolynomial bs := rfl

theorem rootPolynomial_append (as bs : List ℝ) :
    rootPolynomial (as ++ bs) = rootPolynomial as * rootPolynomial bs := by
  simp [rootPolynomial]

theorem aeval_rootPolynomial (bs : List ℝ) :
    aeval backward (rootPolynomial bs) = lowerProduct (bs.map (fun β _ => β)) := by
  induction bs with
  | nil => simp
  | cons b bs ih => simp [ih, aeval_linear_factor]

theorem forward_pow_apply (q : ℕ) (x : Seq) (n : ℕ) : (forward ^ q) x n = x (n+q) := by
  induction q generalizing n with
  | zero => simp
  | succ q ih =>
    rw [pow_succ']
    change (forward ^ q) x (n+1) = x (n+(q+1))
    rw [ih]
    congr 1
    omega

theorem backward_pow_apply (k : ℕ) (x : Seq) (n : ℕ) :
    (backward ^ k) x n = if k ≤ n then x (n-k) else 0 := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ']
    cases n with
    | zero => change backward ((backward ^ k) x) 0 = _; simp
    | succ n =>
      change backward ((backward ^ k) x) (n+1) = _
      rw [backward_succ, ih]
      simp

theorem upper_shift_identity (β : ℝ) (q : ℕ) :
    upper (fun _ => β) * forward ^ q = forward ^ (q+1) * lower (fun _ => β) := by
  ext x n
  change β * ((forward ^ q) x n) + (forward ^ q) x (n+1) =
    (forward ^ (q+1)) (lower (fun _ => β) x) n
  rw [forward_pow_apply, forward_pow_apply, forward_pow_apply]
  rw [show n+(q+1) = (n+q)+1 by omega, lower_succ]
  rw [show n+1+q = n+q+1 by omega]
  ring

/-- The exact upper--lower product corresponding to the factored symbol. -/
theorem upper_root_product (bs : List ℝ) :
    upperProduct (bs.map (fun β _ => β)) =
      forward ^ bs.length * aeval backward (rootPolynomial bs) := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    simp only [List.map_cons, upperProduct_cons, List.length_cons,
      rootPolynomial_cons, map_mul, aeval_linear_factor]
    rw [ih, ← mul_assoc, upper_shift_identity, mul_assoc]

/-- The Toeplitz operator for the Laurent symbol z^(-q) P(z). -/
def symbolOperator (q : ℕ) (P : ℝ[X]) : Op := forward ^ q * aeval backward P

/-- Zero extension of polynomial coefficients for negative differences. -/
def symbolMatrix (q : ℕ) (P : ℝ[X]) : Matrix ℕ ℕ ℝ :=
  fun i j => if j ≤ i+q then P.coeff (i+q-j) else 0

def basis (j : ℕ) : Seq := fun n => if n = j then 1 else 0
def opMatrix (A : Op) : Matrix ℕ ℕ ℝ := fun i j => A (basis j) i

theorem aeval_basis (P : ℝ[X]) (j n : ℕ) :
    (aeval backward P) (basis j) n = if j ≤ n then P.coeff (n-j) else 0 := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    simp only [map_add, LinearMap.add_apply, Pi.add_apply, coeff_add, hP, hQ]
    split_ifs <;> simp
  | monomial k c =>
    rw [aeval_monomial, algebraMap_op]
    change c * ((backward ^ k) (basis j) n) = _
    rw [backward_pow_apply]
    simp only [basis, coeff_monomial]
    by_cases hj : j ≤ n
    · by_cases hk : k = n-j
      · subst k
        simp [hj, show n-j ≤ n by omega, show n-(n-j) = j by omega]
      · have hne : k ≤ n → n-k ≠ j := by omega
        by_cases hkn : k ≤ n <;> simp [hj, hk, hkn, hne]
    · have hne : n-k ≠ j := by omega
      by_cases hkn : k ≤ n <;> simp [hj, hkn, hne]

/-- The formalized operator has exactly the entries used in the paper. -/
theorem symbolOperator_matrix (q : ℕ) (P : ℝ[X]) :
    opMatrix (symbolOperator q P) = symbolMatrix q P := by
  ext i j
  change (forward ^ q) ((aeval backward P) (basis j)) i = _
  rw [forward_pow_apply, aeval_basis]
  rfl

theorem factored_symbol_operator (ω : ℝ) (us as : List ℝ) :
    symbolOperator us.length (C ω * rootPolynomial (us ++ as)) =
      diagonal (fun _ => ω) *
        (upperProduct (us.map (fun β _ => β)) * lowerProduct (as.map (fun β _ => β))) := by
  rw [symbolOperator, rootPolynomial_append, map_mul, map_mul, aeval_C, algebraMap_op,
    ← aeval_rootPolynomial, upper_root_product]
  simp only [← mul_assoc]
  rw [constant_diagonal_commutes ω (forward ^ us.length)]

/-- A factored polynomial with positive root parameters produces a global
normalized PBF, whose entries are bounded above and away from zero. -/
theorem factored_symbol_has_bounded_PBF (ω : ℝ) (hω : 0 < ω) (us as : List ℝ)
    (hu : ∀ β ∈ us, 0 < β) (ha : ∀ β ∈ as, 0 < β) :
    HasBoundedPBF as.length us.length
      (symbolOperator us.length (C ω * rootPolynomial (us ++ as))) := by
  rw [factored_symbol_operator]
  have hc := upper_lower_has_bounded_PBF ω hω (us.map (fun β _ => β))
    (as.map (fun β _ => β))
  simp only [List.length_map] at hc
  apply hc
  · intro u hu'
    obtain ⟨β, hβ, rfl⟩ := List.mem_map.mp hu'
    exact boundedPositive_const (hu β hβ)
  · intro a ha'
    obtain ⟨β, hβ, rfl⟩ := List.mem_map.mp ha'
    exact boundedPositive_const (ha β hβ)

#print axioms symbolOperator_matrix
#print axioms factored_symbol_has_bounded_PBF
end BTP.Toeplitz
