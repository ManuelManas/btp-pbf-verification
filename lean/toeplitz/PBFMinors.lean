import PositiveMinors

/-! From a global PBF to positivity of every finite admissible minor. -/

open Matrix Finset
noncomputable section
namespace BTP.Toeplitz

theorem opMatrix_one : opMatrix (1 : Op) = 1 := by
  ext i j
  simp [opMatrix, basis, Matrix.one_apply]

theorem opMatrix_lower_mul (a : Seq) (A : Op) :
    opMatrix (lower a * A) = lowerRows a (opMatrix A) := by
  ext i j
  rfl

theorem opMatrix_upper_mul (b : Seq) (A : Op) :
    opMatrix (unitUpper b * A) = upperRows b (opMatrix A) := by
  ext i j
  rfl

theorem diagonal_mul_minor (d : Seq) (A : Op) {k : ℕ} (I J : Fin k → ℕ) :
    ((opMatrix (diagonal d * A)).submatrix I J).det =
      (∏ i, d (I i)) * ((opMatrix A).submatrix I J).det := by
  exact Matrix.det_mul_column (fun i => d (I i)) ((opMatrix A).submatrix I J)

theorem diagonal_mul_BTP {p q : ℕ} {d : Seq} (hd : ∀ n, 0 < d n)
    {A : Op} (hA : BandedTP p q (opMatrix A)) : BandedTP p q (opMatrix (diagonal d * A)) := by
  constructor
  · intro k I J hI hJ
    rw [diagonal_mul_minor]
    exact mul_nonneg (Finset.prod_nonneg (fun i _ => (hd (I i)).le)) (hA.1 I J hI hJ)
  · intro k I J hI hJ ha
    rw [diagonal_mul_minor]
    exact mul_pos (Finset.prod_pos (fun i _ => hd (I i))) (hA.2 I J hI hJ ha)

theorem unitUpperProduct_BTP (bs : List Seq) (hb : ∀ b ∈ bs, ∀ n, 0 < b n) :
    BandedTP 0 bs.length (opMatrix (unitUpperProduct bs)) := by
  induction bs with
  | nil => simpa only [unitUpperProduct_nil, opMatrix_one, List.length_nil] using identity_BTP
  | cons b bs ih =>
    rw [unitUpperProduct_cons, opMatrix_upper_mul, List.length_cons]
    exact upperRows_BTP (hb b (by simp)) (ih (fun a ha => hb a (by simp [ha])))

theorem lowerProduct_mul_BTP (as : List Seq) (ha : ∀ a ∈ as, ∀ n, 0 < a n)
    {p q : ℕ} {A : Op} (hA : BandedTP p q (opMatrix A)) :
    BandedTP (as.length+p) q (opMatrix (lowerProduct as * A)) := by
  induction as with
  | nil => simpa using hA
  | cons a as ih =>
    rw [lowerProduct_cons, mul_assoc, opMatrix_lower_mul]
    have h := lowerRows_BTP (ha a (by simp)) (ih (fun b hb => ha b (by simp [hb])))
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

def HasPBF (p q : ℕ) (T : Op) : Prop :=
  ∃ as bs : List Seq, ∃ d : Seq,
    as.length = p ∧ bs.length = q ∧
    (∀ a ∈ as, ∀ n, 0 < a n) ∧ (∀ b ∈ bs, ∀ n, 0 < b n) ∧
    (∀ n, 0 < d n) ∧ T = lowerProduct as * diagonal d * unitUpperProduct bs

theorem HasBoundedPBF.hasPBF {p q : ℕ} {T : Op} (h : HasBoundedPBF p q T) : HasPBF p q T := by
  obtain ⟨as, bs, d, hla, hlb, ha, hb, hd, he⟩ := h
  exact ⟨as, bs, d, hla, hlb, fun a ha' n => (ha a ha').pos n,
    fun b hb' n => (hb b hb').pos n, hd.pos, he⟩

/-- Positivity holds for all orders and arbitrary increasing index lists. -/
theorem PBF_implies_BTP {p q : ℕ} {T : Op} (h : HasPBF p q T) :
    BandedTP p q (opMatrix T) := by
  obtain ⟨as, bs, d, hla, hlb, ha, hb, hd, rfl⟩ := h
  rw [mul_assoc]
  have h := lowerProduct_mul_BTP as ha (diagonal_mul_BTP hd (unitUpperProduct_BTP bs hb))
  simpa only [Nat.add_zero, hla, hlb] using h

theorem PBF_implies_TN {p q : ℕ} {T : Op} (h : HasPBF p q T) : TN (opMatrix T) :=
  (PBF_implies_BTP h).1

/-- The arbitrary index shift used before applying the polynomial case of Edrei. -/
theorem symbolMatrix_TN_iff_shift_zero (q : ℕ) (P : Polynomial ℝ) :
    TN (symbolMatrix q P) ↔ TN (symbolMatrix 0 P) := by
  constructor
  · intro h k I J hI hJ
    let J' : Fin k → ℕ := fun i => J i+q
    have hj' : StrictMono J' := fun i j hij => Nat.add_lt_add_right (hJ hij) q
    have he : (symbolMatrix q P).submatrix I J' = (symbolMatrix 0 P).submatrix I J := by
      ext i j
      have heq : I i + q - (J j + q) = I i - J j := by omega
      simp [symbolMatrix, J', heq]
    rw [← he]
    exact h I J' hI hj'
  · intro h k I J hI hJ
    let I' : Fin k → ℕ := fun i => I i+q
    have hi' : StrictMono I' := fun i j hij => Nat.add_lt_add_right (hI hij) q
    have he : (symbolMatrix 0 P).submatrix I' J = (symbolMatrix q P).submatrix I J := by
      ext i j
      simp [symbolMatrix, I']
    rw [← he]
    exact h I' J hi' hJ

#print axioms PBF_implies_BTP
#print axioms symbolMatrix_TN_iff_shift_zero
end BTP.Toeplitz
