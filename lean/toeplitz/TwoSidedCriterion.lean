import Necessity

/-! # Uniqueness of normalized triangular products and the full two-sided criterion -/
open Matrix Finset
noncomputable section
namespace BTP.SemiInfinite
open InverseBounds

def UnitLowerSection {d : ℕ} (A : Square d) : Prop :=
  (∀ i j, i.val < j.val → A i j = 0) ∧ ∀ i, A i i = 1

theorem unitLowerSection_product (d p : ℕ) (a : Entries) :
    UnitLowerSection (lowerProduct d a p) := by
  constructor
  · intro i j hij
    rw [lowerProduct_entry, ite_eq_right (by omega)]
  · intro i
    simp [lowerProduct_entry]

theorem unitLowerSection_inverse (d p : ℕ) (a : Entries) :
    UnitLowerSection ((lowerProduct d a p)⁻¹) := by
  have he : (lowerProduct d a p)⁻¹ = checker (qProduct d a p) := by
    rw [qProduct_signed_inverse, checker_twice]
  rw [he]
  constructor
  · intro i j hij
    rw [checker_entry, inverseEntries_finite, inverseEntries_upper a p _ _ hij]
    ring
  · intro i
    rw [checker_entry, inverseEntries_finite, inverseEntries_diagonal, mul_one, sign_square]

theorem unitLowerSection_mul {d : ℕ} {A B : Square d}
    (hA : UnitLowerSection A) (hB : UnitLowerSection B) : UnitLowerSection (A * B) := by
  constructor
  · intro i j hij
    rw [Matrix.mul_apply]
    apply sum_eq_zero
    intro k _
    by_cases hk : i.val < k.val
    · rw [hA.1 i k hk, zero_mul]
    · rw [hB.1 k j (by omega), mul_zero]
  · intro i
    rw [Matrix.mul_apply, sum_eq_single i, hA.2 i, hB.2 i, mul_one]
    · intro k _ hki
      have hne : k.val ≠ i.val := fun e => hki (Fin.ext e)
      by_cases hk : i.val < k.val
      · rw [hA.1 i k hk, zero_mul]
      · rw [hB.1 k i (by omega), mul_zero]
    · simp

theorem unit_triangular_diagonal_unique {d : ℕ} {X Y : Square d} (D : Fin d → ℝ)
    (hX : UnitLowerSection X) (hY : UnitLowerSection Y) (hD : ∀ i, D i ≠ 0)
    (he : X * Matrix.diagonal D = Matrix.diagonal D * Y.transpose) : X = 1 ∧ Y = 1 := by
  have hent : ∀ i j, X i j * D j = D i * Y j i := by
    intro i j
    have h := congrArg (fun M : Square d => M i j) he
    simpa only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transpose_apply] using h
  constructor
  · ext i j
    by_cases hij : i = j
    · subst j; simp [hX.2 i]
    · simp only [Matrix.one_apply, ite_eq_right hij]
      by_cases hlt : i.val < j.val
      · exact hX.1 i j hlt
      · have hne : i.val ≠ j.val := fun e => hij (Fin.ext e)
        have h := hent i j
        rw [hY.1 j i (by omega), mul_zero] at h
        exact (mul_eq_zero.mp h).resolve_right (hD j)
  · ext i j
    by_cases hij : i = j
    · subst j; simp [hY.2 i]
    · simp only [Matrix.one_apply, ite_eq_right hij]
      by_cases hlt : i.val < j.val
      · exact hY.1 i j hlt
      · have hne : i.val ≠ j.val := fun e => hij (Fin.ext e)
        have h := hent j i
        rw [hX.1 j i (by omega), zero_mul] at h
        exact (mul_eq_zero.mp h.symm).resolve_left (hD j)

theorem normalized_products_unique (p q : ℕ) (a b c e : Entries) (D : ℕ → ℝ)
    (hD : ∀ n, D n ≠ 0)
    (he : ∀ d, triangularSections p q b e D d = triangularSections p q a c D d) :
    SameProduct p b a ∧ SameProduct q e c := by
  have hall : ∀ d, lowerProduct d b p = lowerProduct d a p ∧
      lowerProduct d e q = lowerProduct d c q := by
    intro d
    let A := lowerProduct d a p
    let B := lowerProduct d b p
    let C := lowerProduct d c q
    let E := lowerProduct d e q
    let DD := Matrix.diagonal (fun i : Fin d => D i.val)
    have hA : IsUnit A.det := by dsimp [A]; rw [lowerProduct_det]; exact isUnit_one
    have hE : IsUnit E.det := by dsimp [E]; rw [lowerProduct_det]; exact isUnit_one
    have hU : E.transpose * E⁻¹.transpose = 1 := by
      rw [← Matrix.transpose_mul, Matrix.nonsing_inv_mul E hE, Matrix.transpose_one]
    have he' : B * DD * E.transpose = A * DD * C.transpose := he d
    have hmain : (A⁻¹ * B) * DD = DD * (E⁻¹ * C).transpose := by
      calc
        _ = (A⁻¹ * B) * DD * (E.transpose * E⁻¹.transpose) := by rw [hU, Matrix.mul_one]
        _ = A⁻¹ * (B * DD * E.transpose) * E⁻¹.transpose := by noncomm_ring
        _ = A⁻¹ * (A * DD * C.transpose) * E⁻¹.transpose := by rw [he']
        _ = (A⁻¹ * A) * DD * (C.transpose * E⁻¹.transpose) := by noncomm_ring
        _ = _ := by rw [Matrix.nonsing_inv_mul A hA, Matrix.one_mul, Matrix.transpose_mul]
    obtain ⟨hX, hY⟩ := unit_triangular_diagonal_unique (fun i : Fin d => D i.val)
      (unitLowerSection_mul (unitLowerSection_inverse d p a) (unitLowerSection_product d p b))
      (unitLowerSection_mul (unitLowerSection_inverse d q e) (unitLowerSection_product d q c))
      (fun i => hD i.val) hmain
    constructor
    · change B = A
      calc
        B = A * (A⁻¹ * B) := by rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv A hA, Matrix.one_mul]
        _ = A := by rw [hX, Matrix.mul_one]
    · change E = C
      symm
      calc
        C = E * (E⁻¹ * C) := by rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv E hE, Matrix.one_mul]
        _ = E := by rw [hY, Matrix.mul_one]
  exact ⟨fun d => (hall d).1, fun d => (hall d).2⟩

/-- The full necessary-and-sufficient criterion for all p+q-2 limits. -/
theorem two_sided_PBF_iff_positive_limits {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {a c : Entries} {D : ℕ → ℝ}
    (ha : Metelmann p a) (hc : Metelmann q c) (hD : ∀ n, 0 < D n) :
    HasTwoSidedPBF p q a c D ↔ ∀ i : ObstructionIndex p q, 0 < twoSidedLimit p q a c i := by
  constructor
  · rintro ⟨_, b, e, hb, he, hprod⟩
    obtain ⟨hbprod, heprod⟩ := normalized_products_unique p q a b c e D (fun n => (hD n).ne') hprod
    intro i
    cases i with
    | inl k => exact PBF_gives_positive_limits ha ⟨b, hb, hbprod⟩ k.val (by omega)
    | inr k => exact PBF_gives_positive_limits hc ⟨e, he, heprod⟩ k.val (by omega)
  · intro hl
    exact (p_add_q_sub_two_positive_limits hp hq ha hc hD hl).1

#print axioms normalized_products_unique
#print axioms two_sided_PBF_iff_positive_limits
end BTP.SemiInfinite
