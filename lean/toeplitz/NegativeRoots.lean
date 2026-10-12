import ToeplitzSymbol
import Mathlib.Algebra.Polynomial.Splits

/-! All roots are real and negative precisely when the nonzero polynomial
splits over ℝ and all members of its root multiset are negative. Multiplicities
are retained throughout. -/

open Polynomial
noncomputable section
namespace BTP.Toeplitz

def NegativeRoots (P : ℝ[X]) : Prop :=
  P.Splits ∧ ∀ r ∈ P.roots, r < 0

theorem rootPolynomial_zero_coeff (bs : List ℝ) : (rootPolynomial bs).coeff 0 = 1 := by
  induction bs with
  | nil => simp
  | cons b bs ih => simp [Polynomial.mul_coeff_zero, ih]

theorem linear_root_normalization {r : ℝ} (hr : r ≠ 0) :
    X - C r = C (-r) * (1 + C ((-r)⁻¹) * X) := by
  rw [mul_add, mul_one, ← mul_assoc, ← C_mul, mul_inv_cancel₀ (neg_ne_zero.mpr hr), C_1, one_mul]
  simp only [map_neg]
  ring

theorem normalize_root_list (rs : List ℝ) (hr : ∀ r ∈ rs, r ≠ 0) :
    (rs.map (fun r => (X : ℝ[X]) - C r)).prod =
      C ((rs.map (fun r => -r)).prod) * rootPolynomial (rs.map (fun r => (-r)⁻¹)) := by
  induction rs with
  | nil => simp
  | cons r rs ih =>
    simp only [List.map_cons, List.prod_cons, rootPolynomial_cons]
    rw [linear_root_normalization (hr r (by simp)), ih (fun s hs => hr s (by simp [hs])), C_mul]
    ring

/-- The root parametrization follows from the actual roots, including repetitions. -/
theorem negativeRoots_factorization (P : ℝ[X]) (hP : NegativeRoots P) :
    ∃ bs : List ℝ, (∀ β ∈ bs, 0 < β) ∧ bs.length = P.natDegree ∧
      P = C (P.coeff 0) * rootPolynomial bs := by
  let rs := P.roots.toList
  let bs := rs.map (fun r => (-r)⁻¹)
  have hneg : ∀ r ∈ rs, r < 0 := by
    intro r hr
    exact hP.2 r (Multiset.mem_toList.mp hr)
  have hnorm := normalize_root_list rs (fun r hr => (hneg r hr).ne)
  have he : P = C (P.leadingCoeff * (rs.map (fun r => -r)).prod) * rootPolynomial bs := by
    calc
      P = C P.leadingCoeff * (rs.map (fun r => X - C r)).prod := by
        simpa only [rs, Multiset.prod_map_toList] using hP.1.eq_prod_roots
      _ = _ := by rw [hnorm, C_mul]; ring
  have hc := congrArg (fun Q : ℝ[X] => Q.coeff 0) he
  simp only [Polynomial.mul_coeff_zero, coeff_C_zero, rootPolynomial_zero_coeff, mul_one] at hc
  refine ⟨bs, ?_, ?_, ?_⟩
  · intro β hβ
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hβ
    exact inv_pos.mpr (neg_pos.mpr (hneg r hr))
  · simp only [bs, List.length_map, rs, Multiset.length_toList]
    exact hP.1.natDegree_eq_card_roots.symm
  · rw [hc]
    exact he

theorem rootPolynomial_splits (bs : List ℝ) : (rootPolynomial bs).Splits := by
  induction bs with
  | nil => simp
  | cons β bs ih =>
    rw [rootPolynomial_cons]
    apply Polynomial.Splits.mul _ ih
    apply Polynomial.Splits.of_natDegree_le_one
    apply Polynomial.natDegree_add_le_of_degree_le
    · simp
    · exact Polynomial.natDegree_le_of_degree_le (Polynomial.degree_C_mul_X_le β)

theorem rootPolynomial_eval_positive (bs : List ℝ) (hb : ∀ β ∈ bs, 0 < β)
    (x : ℝ) (hx : 0 ≤ x) : 0 < (rootPolynomial bs).eval x := by
  induction bs with
  | nil => simp
  | cons β bs ih =>
    simp only [rootPolynomial_cons, eval_mul, eval_add, eval_one, eval_C, eval_X]
    apply mul_pos
    · have h := mul_nonneg (hb β (by simp)).le hx
      linarith
    · exact ih (fun b h => hb b (by simp [h]))

theorem factored_polynomial_negativeRoots (ω : ℝ) (hω : 0 < ω)
    (bs : List ℝ) (hb : ∀ β ∈ bs, 0 < β) : NegativeRoots (C ω * rootPolynomial bs) := by
  refine ⟨(rootPolynomial_splits bs).C_mul ω, ?_⟩
  intro r hr
  by_contra h
  have hp := mul_pos hω (rootPolynomial_eval_positive bs hb r (le_of_not_gt h))
  have he := Polynomial.isRoot_of_mem_roots hr
  change (C ω * rootPolynomial bs).eval r = 0 at he
  simp only [eval_mul, eval_C] at he
  linarith

theorem negativeRoots_has_bounded_PBF (p q : ℕ) (P : ℝ[X])
    (hdeg : P.natDegree = p+q) (hzero : 0 < P.coeff 0) (hP : NegativeRoots P) :
    HasBoundedPBF p q (symbolOperator q P) := by
  obtain ⟨bs, hb, hlen, he⟩ := negativeRoots_factorization P hP
  have ht : (bs.take q).length = q := by simp [List.length_take, hlen, hdeg]
  have hd : (bs.drop q).length = p := by simp [List.length_drop, hlen, hdeg]
  have h := factored_symbol_has_bounded_PBF (P.coeff 0) hzero (bs.take q) (bs.drop q)
    (fun β hβ => hb β (List.mem_of_mem_take hβ)) (fun β hβ => hb β (List.mem_of_mem_drop hβ))
  rw [List.take_append_drop, ht, hd, ← he] at h
  exact h

#print axioms negativeRoots_factorization
#print axioms negativeRoots_has_bounded_PBF
end BTP.Toeplitz
