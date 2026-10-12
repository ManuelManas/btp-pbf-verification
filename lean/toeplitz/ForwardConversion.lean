import ToeplitzSymbol

/-! Converting q factors of a triangular product into upper factors.
The entries may depend on the row; no polynomial root factorization is used. -/

noncomputable section
namespace BTP.Toeplitz

theorem variable_upper_shift (a : Seq) (q : ℕ) :
    upper (fun n => a (n+q+1)) * forward^q = forward^(q+1) * lower a := by
  ext x n
  change a (n+q+1) * ((forward^q) x n) + (forward^q) x (n+1) =
    (forward^(q+1)) (lower a x) n
  rw [forward_pow_apply, forward_pow_apply, forward_pow_apply]
  rw [show n+(q+1) = (n+q)+1 by omega, lower_succ,
    show n+1+q = n+q+1 by omega]
  ring

def raisedUpper : List Seq → List Seq
  | [] => []
  | a :: as => (fun n => a (n+as.length+1)) :: raisedUpper as

theorem raisedUpper_length (as : List Seq) : (raisedUpper as).length = as.length := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [raisedUpper, ih]

theorem raisedUpper_bounded (as : List Seq) (ha : ∀ a ∈ as, BoundedPositive a) :
    ∀ u ∈ raisedUpper as, BoundedPositive u := by
  induction as with
  | nil => simp [raisedUpper]
  | cons a as ih =>
    intro u hu
    rcases List.mem_cons.mp hu with rfl | hu
    · exact (ha a (by simp)).comp (fun n => n+as.length+1)
    · exact ih (fun b hb => ha b (by simp [hb])) u hu

theorem upper_conversion (as : List Seq) :
    upperProduct (raisedUpper as) = forward^as.length * lowerProduct as := by
  induction as with
  | nil => simp [raisedUpper]
  | cons a as ih =>
    simp only [raisedUpper, upperProduct_cons, lowerProduct_cons, List.length_cons]
    rw [ih, ← mul_assoc, variable_upper_shift, mul_assoc]

/-- A positive triangular factorization of the coefficient Toeplitz operator
produces a PBF of every admissible Laurent shift of that operator. -/
theorem triangular_factorization_to_PBF (as : List Seq) (p q : ℕ)
    (hlen : as.length = p+q) (ha : ∀ a ∈ as, BoundedPositive a)
    (ω : ℝ) (hω : 0 < ω) :
    HasBoundedPBF p q (diagonal (fun _ => ω) * forward^q * lowerProduct as) := by
  let left := as.take q
  let right := as.drop q
  have hl : left.length = q := by simp [left, hlen]
  have hr : right.length = p := by simp [right, hlen]
  have hlu : ∀ u ∈ raisedUpper left, BoundedPositive u :=
    raisedUpper_bounded left (fun a ha' => ha a (List.mem_of_mem_take ha'))
  have hra : ∀ a ∈ right, BoundedPositive a :=
    fun a ha' => ha a (List.mem_of_mem_drop ha')
  have h := upper_lower_has_bounded_PBF ω hω (raisedUpper left) right hlu hra
  rw [raisedUpper_length, hl, hr] at h
  rw [upper_conversion, hl] at h
  have he : lowerProduct as = lowerProduct left * lowerProduct right := by
    rw [show lowerProduct left * lowerProduct right = lowerProduct (left ++ right) by
      simp [lowerProduct]]
    congr 1
    exact (List.take_append_drop q as).symm
  simpa only [he, mul_assoc] using h

#print axioms triangular_factorization_to_PBF
end BTP.Toeplitz
