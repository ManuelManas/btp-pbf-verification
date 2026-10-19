import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-! Finite-section algebra for the variation of normalized LDU.
No uniform bound on the triangular inverse matrices is assumed. -/
open Matrix Finset
noncomputable section
namespace BTP.Stability.BandLDU
variable {n : ℕ}
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

def Lower (A : Mat n) : Prop := ∀ i j, i < j → A i j = 0
def Upper (A : Mat n) : Prop := ∀ i j, j < i → A i j = 0
def StrictLower (A : Mat n) : Prop := ∀ i j, i ≤ j → A i j = 0
def StrictUpper (A : Mat n) : Prop := ∀ i j, j ≤ i → A i j = 0
def Diag (A : Mat n) : Prop := ∀ i j, i ≠ j → A i j = 0

def lowerPart (V : Mat n) : Mat n := fun i j => if j < i then V i j else 0
def diagPart (V : Mat n) : Mat n := Matrix.diagonal (fun i => V i i)
def upperPart (V : Mat n) : Mat n := fun i j => if i < j then V i j else 0

theorem lowerPart_strict (V : Mat n) : StrictLower (lowerPart V) := by
  intro i j h; simp [lowerPart, not_lt.mpr h]
theorem upperPart_strict (V : Mat n) : StrictUpper (upperPart V) := by
  intro i j h; simp [upperPart, not_lt.mpr h]
theorem diagPart_diag (V : Mat n) : Diag (diagPart V) := by
  intro i j h; simp [diagPart, Matrix.diagonal, h]

theorem parts_sum (V : Mat n) : lowerPart V + diagPart V + upperPart V = V := by
  ext i j
  rcases lt_trichotomy i j with h | h | h
  · simp [lowerPart, upperPart, diagPart, h, not_lt.mpr h.le, ne_of_lt h]
  · subst j; simp [lowerPart, upperPart, diagPart]
  · simp [lowerPart, upperPart, diagPart, h, not_lt.mpr h.le, ne_of_gt h]

theorem lower_mul_strict {A B : Mat n} (hA : Lower A) (hB : StrictLower B) :
    StrictLower (A * B) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply sum_eq_zero
  intro k _
  by_cases hik : i < k
  · rw [hA i k hik, zero_mul]
  · rw [hB k j (le_trans (le_of_not_gt hik) hij), mul_zero]

theorem upper_strict_mul {A B : Mat n} (hA : StrictUpper A) (hB : Upper B) :
    StrictUpper (A * B) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply sum_eq_zero
  intro k _
  by_cases hki : k ≤ i
  · rw [hA i k hki, zero_mul]
  · rw [hB k j (lt_of_le_of_lt hij (lt_of_not_ge hki)), mul_zero]

theorem strict_mul_diagonal {A : Mat n} (hA : StrictLower A) (d : Fin n → ℝ) :
    StrictLower (A * Matrix.diagonal d) := by
  intro i j hij; simp [Matrix.mul_diagonal, hA i j hij]
theorem diagonal_mul_strict {A : Mat n} (hA : StrictUpper A) (d : Fin n → ℝ) :
    StrictUpper (Matrix.diagonal d * A) := by
  intro i j hij; simp [Matrix.diagonal_mul, hA i j hij]

theorem parts_unique {A Z C V : Mat n} (hA : StrictLower A)
    (hZ : Diag Z) (hC : StrictUpper C) (he : A + Z + C = V) :
    A = lowerPart V ∧ Z = diagPart V ∧ C = upperPart V := by
  have hent (i j : Fin n) : A i j + Z i j + C i j = V i j :=
    congrArg (fun M : Mat n => M i j) he
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    by_cases h : j < i
    · have ht := hent i j
      rw [hZ i j (ne_of_gt h), hC i j h.le] at ht
      simpa [lowerPart, h] using ht
    · simp [lowerPart, h, hA i j (le_of_not_gt h)]
  · ext i j
    by_cases h : i = j
    · subst j
      have ht := hent i i
      rw [hA i i le_rfl, hC i i le_rfl] at ht
      simpa [diagPart] using ht
    · simp [diagPart, Matrix.diagonal, h, hZ i j h]
  · ext i j
    by_cases h : i < j
    · have ht := hent i j
      rw [hA i j h.le, hZ i j (ne_of_lt h)] at ht
      simpa [upperPart, h] using ht
    · simp [upperPart, h, hC i j (le_of_not_gt h)]

def variation (L D U X Z Y : Mat n) : Mat n :=
  X * D * U + L * Z * U + L * D * Y

theorem variation_formula (L Li U Ui : Mat n) (d : Fin n → ℝ)
    (hL : L * Li = 1) (hU : Ui * U = 1) (hd : ∀ i, d i ≠ 0) (E : Mat n) :
    let D := Matrix.diagonal d
    let Di := Matrix.diagonal (fun i => (d i)⁻¹)
    let V := Li * E * Ui
    variation L D U (L * lowerPart V * Di) (diagPart V) (Di * upperPart V * U) = E := by
  dsimp only
  have hD : Matrix.diagonal (fun i => (d i)⁻¹) * Matrix.diagonal d = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j; simp [hd]
    · simp [Matrix.diagonal, hij]
  have hD' : Matrix.diagonal d * Matrix.diagonal (fun i => (d i)⁻¹) = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j; simp [hd]
    · simp [Matrix.diagonal, hij]
  let V := Li * E * Ui
  change variation L (Matrix.diagonal d) U
    (L * lowerPart V * Matrix.diagonal (fun i => (d i)⁻¹)) (diagPart V)
    (Matrix.diagonal (fun i => (d i)⁻¹) * upperPart V * U) = E
  unfold variation
  calc
    _ = L * lowerPart V * U + L * diagPart V * U + L * upperPart V * U := by
      have ht₁ : (L * lowerPart V * Matrix.diagonal (fun i => (d i)⁻¹)) * Matrix.diagonal d * U = L * lowerPart V * U := by
        calc
          _ = L * lowerPart V * (Matrix.diagonal (fun i => (d i)⁻¹) * Matrix.diagonal d) * U := by noncomm_ring
          _ = _ := by rw [hD]; simp
      have ht₂ : L * Matrix.diagonal d * (Matrix.diagonal (fun i => (d i)⁻¹) * upperPart V * U) = L * upperPart V * U := by
        calc
          _ = L * (Matrix.diagonal d * Matrix.diagonal (fun i => (d i)⁻¹)) * upperPart V * U := by noncomm_ring
          _ = _ := by rw [hD']; simp
      rw [ht₁, ht₂]
    _ = L * (lowerPart V + diagPart V + upperPart V) * U := by noncomm_ring
    _ = L * V * U := by rw [parts_sum]
    _ = (L * Li) * E * (Ui * U) := by dsimp [V]; noncomm_ring
    _ = E := by rw [hL, hU]; simp

theorem variation_formula_triangular (L U V : Mat n) (d : Fin n → ℝ)
    (hL : Lower L) (hU : Upper U) :
    StrictLower (L * lowerPart V * Matrix.diagonal (fun i => (d i)⁻¹)) ∧
    Diag (diagPart V) ∧
    StrictUpper (Matrix.diagonal (fun i => (d i)⁻¹) * upperPart V * U) := by
  refine ⟨strict_mul_diagonal (lower_mul_strict hL (lowerPart_strict V)) _,
    diagPart_diag V, ?_⟩
  exact upper_strict_mul (diagonal_mul_strict (upperPart_strict V) _) hU

theorem variation_diagonal (L Li U Ui X Z Y : Mat n) (d : Fin n → ℝ)
    (hL : Li * L = 1) (hU : U * Ui = 1)
    (hLi : Lower Li) (hUi : Upper Ui)
    (hX : StrictLower X) (hZ : Diag Z) (hY : StrictUpper Y) :
    Z = diagPart (Li * variation L (Matrix.diagonal d) U X Z Y * Ui) := by
  have he : Li * variation L (Matrix.diagonal d) U X Z Y * Ui =
      Li * X * Matrix.diagonal d + Z + Matrix.diagonal d * Y * Ui := by
    unfold variation
    simp only [Matrix.mul_add, Matrix.add_mul]
    have h₁ : Li * (X * Matrix.diagonal d * U) * Ui = Li * X * Matrix.diagonal d := by
      simp only [Matrix.mul_assoc, hU, Matrix.mul_one]
    have h₂ : Li * (L * Z * U) * Ui = Z := by
      calc
        _ = (Li * L) * Z * (U * Ui) := by noncomm_ring
        _ = Z := by rw [hL, hU]; simp
    have h₃ : Li * (L * Matrix.diagonal d * Y) * Ui = Matrix.diagonal d * Y * Ui := by
      simp only [← Matrix.mul_assoc, hL, Matrix.one_mul]
    rw [h₁, h₂, h₃]
  have ht := parts_unique
    (strict_mul_diagonal (lower_mul_strict hLi hX) d) hZ
    (upper_strict_mul (diagonal_mul_strict hY d) hUi) he.symm
  exact ht.2.1

/-- Uniqueness uses triangularity alone; no inverse entries are assumed
uniformly bounded. This is also the compatibility argument between finite
principal sections. -/
theorem variation_unique (L Li U Ui X Z Y : Mat n) (d : Fin n → ℝ)
    (hL : Li * L = 1) (hL' : L * Li = 1)
    (hU : U * Ui = 1) (hU' : Ui * U = 1)
    (hd : ∀ i, d i ≠ 0) (hLi : Lower Li) (hUi : Upper Ui)
    (hX : StrictLower X) (hZ : Diag Z) (hY : StrictUpper Y) :
    let V := Li * variation L (Matrix.diagonal d) U X Z Y * Ui
    X = L * lowerPart V * Matrix.diagonal (fun i => (d i)⁻¹) ∧
    Z = diagPart V ∧
    Y = Matrix.diagonal (fun i => (d i)⁻¹) * upperPart V * U := by
  dsimp only
  let V := Li * variation L (Matrix.diagonal d) U X Z Y * Ui
  have he : Li * X * Matrix.diagonal d + Z + Matrix.diagonal d * Y * Ui = V := by
    dsimp [V, variation]
    simp only [Matrix.mul_add, Matrix.add_mul]
    have h₁ : Li * (X * Matrix.diagonal d * U) * Ui = Li * X * Matrix.diagonal d := by
      simp only [Matrix.mul_assoc, hU, Matrix.mul_one]
    have h₂ : Li * (L * Z * U) * Ui = Z := by
      calc
        _ = (Li * L) * Z * (U * Ui) := by noncomm_ring
        _ = Z := by rw [hL, hU]; simp
    have h₃ : Li * (L * Matrix.diagonal d * Y) * Ui = Matrix.diagonal d * Y * Ui := by
      simp only [← Matrix.mul_assoc, hL, Matrix.one_mul]
    rw [h₁, h₂, h₃]
  have ht := parts_unique
    (strict_mul_diagonal (lower_mul_strict hLi hX) d) hZ
    (upper_strict_mul (diagonal_mul_strict hY d) hUi) he
  have hD : Matrix.diagonal d * Matrix.diagonal (fun i => (d i)⁻¹) = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i=j
    · subst j; simp [hd]
    · simp [Matrix.diagonal, hij]
  have hD' : Matrix.diagonal (fun i => (d i)⁻¹) * Matrix.diagonal d = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i=j
    · subst j; simp [hd]
    · simp [Matrix.diagonal, hij]
  refine ⟨?_, ht.2.1, ?_⟩
  · change X = L * lowerPart V * Matrix.diagonal (fun i => (d i)⁻¹)
    rw [← ht.1]
    calc
      _ = (L * Li) * X * (Matrix.diagonal d * Matrix.diagonal (fun i => (d i)⁻¹)) := by
        rw [hL', hD]; simp
      _ = _ := by noncomm_ring
  · change Y = Matrix.diagonal (fun i => (d i)⁻¹) * upperPart V * U
    rw [← ht.2.2]
    calc
      _ = (Matrix.diagonal (fun i => (d i)⁻¹) * Matrix.diagonal d) * Y * (Ui * U) := by
        rw [hU', hD']; simp
      _ = _ := by noncomm_ring


def LowerBandwidth (p : ℕ) (A : Mat n) : Prop := ∀ i j, j.val + p < i.val → A i j = 0
def UpperBandwidth (q : ℕ) (A : Mat n) : Prop := ∀ i j, i.val + q < j.val → A i j = 0

theorem lowerBand_mul_upper {p : ℕ} {A B : Mat n}
    (hA : LowerBandwidth p A) (hB : Upper B) : LowerBandwidth p (A*B) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply sum_eq_zero
  intro k _
  by_cases hjk : j < k
  · rw [hB k j hjk, mul_zero]
  · rw [hA i k (by have := le_of_not_gt hjk; omega), zero_mul]

theorem lower_mul_upperBand {q : ℕ} {A B : Mat n}
    (hA : Lower A) (hB : UpperBandwidth q B) : UpperBandwidth q (A*B) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply sum_eq_zero
  intro k _
  by_cases hik : i < k
  · rw [hA i k hik, zero_mul]
  · rw [hB k j (by have := le_of_not_gt hik; omega), mul_zero]

theorem lowerBand_sub {p : ℕ} {A B : Mat n}
    (hA : LowerBandwidth p A) (hB : LowerBandwidth p B) : LowerBandwidth p (A-B) := by
  intro i j hij; simp [hA i j hij, hB i j hij]
theorem upperBand_sub {q : ℕ} {A B : Mat n}
    (hA : UpperBandwidth q A) (hB : UpperBandwidth q B) : UpperBandwidth q (A-B) := by
  intro i j hij; simp [hA i j hij, hB i j hij]

theorem diag_upper_upper (V : Mat n) : Upper (diagPart V + upperPart V) := by
  intro i j hij
  simp [diagPart, Matrix.diagonal, upperPart, ne_of_gt hij, not_lt.mpr hij.le]
theorem lower_diag_lower (V : Mat n) : Lower (lowerPart V + diagPart V) := by
  intro i j hij
  simp [diagPart, Matrix.diagonal, lowerPart, ne_of_lt hij, not_lt.mpr hij.le]

/-- Band preservation for the lower variation, proved without Gaussian elimination. -/
theorem lower_variation_band {p : ℕ} (L Li Uinv E : Mat n)
    (hL : L * Li = 1) (hLb : LowerBandwidth p L)
    (hUi : Upper Uinv) (hE : LowerBandwidth p E) :
    LowerBandwidth p (L * lowerPart (Li * E * Uinv)) := by
  let V := Li * E * Uinv
  have hid : L * lowerPart V = E * Uinv - L * (diagPart V + upperPart V) := by
    have ht : L*V = E*Uinv := by
      dsimp [V]; rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hL, Matrix.one_mul]
    have hs := congrArg (fun A : Mat n => L*A) (parts_sum V)
    rw [ht] at hs
    rw [Matrix.mul_add, Matrix.mul_add] at hs
    rw [Matrix.mul_add]
    exact eq_sub_iff_add_eq.mpr (by simpa only [add_assoc] using hs)
  change LowerBandwidth p (L * lowerPart V)
  rw [hid]
  exact lowerBand_sub (lowerBand_mul_upper hE hUi)
    (lowerBand_mul_upper hLb (diag_upper_upper V))

/-- The transposed support argument for the upper variation. -/
theorem upper_variation_band {q : ℕ} (Linv U Uinv E : Mat n)
    (hU : Uinv * U = 1) (hUb : UpperBandwidth q U)
    (hLi : Lower Linv) (hE : UpperBandwidth q E) :
    UpperBandwidth q (upperPart (Linv * E * Uinv) * U) := by
  let V := Linv * E * Uinv
  have hid : upperPart V * U = Linv * E - (lowerPart V + diagPart V) * U := by
    have ht : V*U = Linv*E := by
      dsimp [V]; rw [Matrix.mul_assoc, hU, Matrix.mul_one]
    have hs := congrArg (fun A : Mat n => A*U) (parts_sum V)
    rw [ht] at hs
    rw [Matrix.add_mul, Matrix.add_mul] at hs
    rw [Matrix.add_mul]
    exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm, add_left_comm, add_assoc] using hs)
  change UpperBandwidth q (upperPart V * U)
  rw [hid]
  exact upperBand_sub (lower_mul_upperBand hLi hE)
    (lower_mul_upperBand (lower_diag_lower V) hUb)


/-- Diagonal multiplication leaves either bandwidth unchanged. -/
theorem lowerBand_mul_diagonal {p : ℕ} {A : Mat n}
    (hA : LowerBandwidth p A) (d : Fin n → ℝ) : LowerBandwidth p (A*Matrix.diagonal d) := by
  intro i j hij; simp [Matrix.mul_diagonal, hA i j hij]
theorem diagonal_mul_upperBand {q : ℕ} {A : Mat n}
    (hA : UpperBandwidth q A) (d : Fin n → ℝ) : UpperBandwidth q (Matrix.diagonal d*A) := by
  intro i j hij; simp [Matrix.diagonal_mul, hA i j hij]

/-- All structural conditions on the solution are proved, including the
finite bandwidths p,q. No preservation-of-band premise is used. -/
theorem variation_formula_bands (L Li U Ui E : Mat n) (d : Fin n → ℝ) (p q : ℕ)
    (hL : L*Li=1) (hU : Ui*U=1)
    (hLb : LowerBandwidth p L) (hUb : UpperBandwidth q U)
    (hLi : Lower Li) (hUi : Upper Ui)
    (hEp : LowerBandwidth p E) (hEq : UpperBandwidth q E) :
    LowerBandwidth p (L*lowerPart (Li*E*Ui)*Matrix.diagonal (fun i => (d i)⁻¹)) ∧
    UpperBandwidth q (Matrix.diagonal (fun i => (d i)⁻¹)*upperPart (Li*E*Ui)*U) := by
  refine ⟨lowerBand_mul_diagonal (lower_variation_band L Li Ui E hL hLb hUi hEp) _, ?_⟩
  rw [Matrix.mul_assoc]
  exact diagonal_mul_upperBand (upper_variation_band Li U Ui E hU hUb hLi hEq) _

/-- Cancellation of the two checkerboard signs in the diagonal forcing.
The signs are explicit data with square one, so the identity also covers
any real diagonal signature conjugation. -/
theorem signed_inverse_diagonal (Li Ui Q R : Mat n) (σ : Fin n → ℝ)
    (hσ : ∀ i, σ i * σ i = 1)
    (hL : ∀ i j, Li i j = σ i * Q i j * σ j)
    (hU : ∀ i j, Ui i j = σ i * R j i * σ j) (i : Fin n) :
    (Li*Ui) i i = ∑ s, Q i s*R i s := by
  rw [Matrix.mul_apply]
  apply sum_congr rfl
  intro s _
  rw [hL, hU]
  calc
    _ = (σ i*σ i)*(σ s*σ s)*(Q i s*R i s) := by ring
    _ = _ := by rw [hσ, hσ]; ring

/-- A genuine solution of the linearized LDU equation in the identity
direction has diagonal equal to the joint signed-inverse row sums. -/
theorem variation_identity_row_sum (L Li U Ui X Z Y Q R : Mat n)
    (d σ : Fin n → ℝ) (hL : Li*L=1) (hU : U*Ui=1)
    (hLi : Lower Li) (hUi : Upper Ui)
    (hX : StrictLower X) (hZ : Diag Z) (hY : StrictUpper Y)
    (hσ : ∀ i, σ i*σ i=1)
    (hQs : ∀ i j, Li i j = σ i*Q i j*σ j)
    (hRs : ∀ i j, Ui i j = σ i*R j i*σ j)
    (he : variation L (Matrix.diagonal d) U X Z Y = 1) (i : Fin n) :
    Z i i = ∑ s, Q i s*R i s := by
  have hz := variation_diagonal L Li U Ui X Z Y d hL hU hLi hUi hX hZ hY
  rw [he, Matrix.mul_one] at hz
  have hi := congrArg (fun A : Mat n => A i i) hz
  simp only [diagPart, Matrix.diagonal_apply_eq] at hi
  exact hi.trans (signed_inverse_diagonal Li Ui Q R σ hσ hQs hRs i)

#print axioms variation_formula
#print axioms variation_formula_bands
#print axioms variation_identity_row_sum
end BTP.Stability.BandLDU
