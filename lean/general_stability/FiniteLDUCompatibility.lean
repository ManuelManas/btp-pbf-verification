import BandSpaces

noncomputable section
open Matrix Finset
namespace BTP.Stability.BandLDU

def principal {n : ℕ} (M : Mat (n+1)) : Mat n :=
  fun i j => M i.castSucc j.castSucc

@[simp] theorem principal_add {n : ℕ} (A B : Mat (n+1)) :
    principal (A+B) = principal A + principal B := rfl

@[simp] theorem principal_diagonal {n : ℕ} (d : Fin (n+1) → ℝ) :
    principal (Matrix.diagonal d) = Matrix.diagonal (fun i => d i.castSucc) := by
  ext i j
  by_cases h : i=j
  · subst j; simp [principal]
  · simp [principal, Matrix.diagonal, h]

theorem principal_lower {n : ℕ} {A : Mat (n+1)} (hA : Lower A) :
    Lower (principal A) := by
  intro i j hij
  exact hA i.castSucc j.castSucc hij

theorem principal_upper {n : ℕ} {A : Mat (n+1)} (hA : Upper A) :
    Upper (principal A) := by
  intro i j hij
  exact hA i.castSucc j.castSucc hij

theorem principal_strictLower {n : ℕ} {A : Mat (n+1)} (hA : StrictLower A) :
    StrictLower (principal A) := by
  intro i j hij
  exact hA i.castSucc j.castSucc hij

theorem principal_strictUpper {n : ℕ} {A : Mat (n+1)} (hA : StrictUpper A) :
    StrictUpper (principal A) := by
  intro i j hij
  exact hA i.castSucc j.castSucc hij

theorem principal_diag {n : ℕ} {A : Mat (n+1)} (hA : Diag A) :
    Diag (principal A) := by
  intro i j hij
  apply hA
  exact fun h => hij (Fin.ext (congrArg (fun k : Fin (n+1) => k.val) h))

theorem principal_mul_lower {n : ℕ} {A : Mat (n+1)} (B : Mat (n+1))
    (hA : Lower A) : principal (A*B) = principal A * principal B := by
  ext i j
  change (∑ k : Fin (n+1), A i.castSucc k*B k j.castSucc) = _
  rw [Fin.sum_univ_castSucc]
  have hz : A i.castSucc (Fin.last n)=0 := hA _ _ (by exact i.isLt)
  simp [hz, Matrix.mul_apply, principal]

theorem principal_mul_upper {n : ℕ} (A : Mat (n+1)) {B : Mat (n+1)}
    (hB : Upper B) : principal (A*B) = principal A * principal B := by
  ext i j
  change (∑ k : Fin (n+1), A i.castSucc k*B k j.castSucc) = _
  rw [Fin.sum_univ_castSucc]
  have hz : B (Fin.last n) j.castSucc=0 := hB _ _ (by exact j.isLt)
  simp [hz, Matrix.mul_apply, principal]

theorem diagonal_lower {n : ℕ} (d : Fin n → ℝ) : Lower (Matrix.diagonal d) := by
  intro i j hij
  simp [Matrix.diagonal, ne_of_lt hij]

theorem diagonal_upper {n : ℕ} (d : Fin n → ℝ) : Upper (Matrix.diagonal d) := by
  intro i j hij
  simp [Matrix.diagonal, ne_of_gt hij]

theorem diag_lower {n : ℕ} {A : Mat n} (hA : Diag A) : Lower A := by
  intro i j h
  exact hA i j (ne_of_lt h)

theorem diag_upper {n : ℕ} {A : Mat n} (hA : Diag A) : Upper A := by
  intro i j h
  exact hA i j (ne_of_gt h)

theorem strictLower_lower {n : ℕ} {A : Mat n} (hA : StrictLower A) : Lower A := by
  intro i j h
  exact hA i j h.le

theorem strictUpper_upper {n : ℕ} {A : Mat n} (hA : StrictUpper A) : Upper A := by
  intro i j h
  exact hA i j h.le

theorem principal_variation {n : ℕ} (L U X Z Y : Mat (n+1)) (d : Fin (n+1) → ℝ)
    (hL : Lower L) (hU : Upper U) (hX : StrictLower X) (_hZ : Diag Z)
    (hY : StrictUpper Y) :
    principal (variation L (Matrix.diagonal d) U X Z Y) =
      variation (principal L) (Matrix.diagonal (fun i => d i.castSucc)) (principal U)
        (principal X) (principal Z) (principal Y) := by
  unfold variation
  rw [principal_add, principal_add]
  rw [principal_mul_upper _ hU, principal_mul_upper _ hU,
    principal_mul_upper _ (strictUpper_upper hY)]
  rw [principal_mul_lower _ (strictLower_lower hX),
    principal_mul_lower _ hL, principal_mul_lower _ hL, principal_diagonal]

/-- Algebraic triangular data on all finite sections. These hypotheses
express formal triangular inverses, not bounded operator inverses. -/
structure SectionData where
  L : (N : ℕ) → Mat N
  Li : (N : ℕ) → Mat N
  U : (N : ℕ) → Mat N
  Ui : (N : ℕ) → Mat N
  d : ℕ → ℝ
  d_ne : ∀ n, d n ≠ 0
  lower_L : ∀ N, Lower (L N)
  lower_Li : ∀ N, Lower (Li N)
  upper_U : ∀ N, Upper (U N)
  upper_Ui : ∀ N, Upper (Ui N)
  Li_L : ∀ N, Li N * L N = 1
  L_Li : ∀ N, L N * Li N = 1
  U_Ui : ∀ N, U N * Ui N = 1
  Ui_U : ∀ N, Ui N * U N = 1
  L_coherent : ∀ N, principal (L (N+1)) = L N
  U_coherent : ∀ N, principal (U (N+1)) = U N

namespace SectionData
open BTP.GeneralStability

def invV (s : SectionData) {p q : ℕ} (E : FullBand p q) (N : ℕ) : Mat N :=
  s.Li N * fullSection E N * s.Ui N

def invX (s : SectionData) {p q : ℕ} (E : FullBand p q) (N : ℕ) : Mat N :=
  s.L N * lowerPart (s.invV E N) * Matrix.diagonal (fun i => (s.d i.val)⁻¹)

def invZ (s : SectionData) {p q : ℕ} (E : FullBand p q) (N : ℕ) : Mat N :=
  diagPart (s.invV E N)

def invY (s : SectionData) {p q : ℕ} (E : FullBand p q) (N : ℕ) : Mat N :=
  Matrix.diagonal (fun i => (s.d i.val)⁻¹) * upperPart (s.invV E N) * s.U N

theorem inv_triangular (s : SectionData) {p q : ℕ} (E : FullBand p q) (N : ℕ) :
    StrictLower (s.invX E N) ∧ Diag (s.invZ E N) ∧ StrictUpper (s.invY E N) :=
  variation_formula_triangular _ _ _ _ (s.lower_L N) (s.upper_U N)

theorem inv_eq (s : SectionData) {p q : ℕ} (E : FullBand p q) (N : ℕ) :
    variation (s.L N) (Matrix.diagonal (fun i => s.d i.val)) (s.U N)
      (s.invX E N) (s.invZ E N) (s.invY E N) = fullSection E N :=
  variation_formula _ _ _ _ _ (s.L_Li N) (s.Ui_U N) (fun i => s.d_ne i.val) _

theorem inv_coherent (s : SectionData) {p q : ℕ} (E : FullBand p q) (N : ℕ) :
    principal (s.invX E (N+1)) = s.invX E N ∧
    principal (s.invZ E (N+1)) = s.invZ E N ∧
    principal (s.invY E (N+1)) = s.invY E N := by
  have ht := s.inv_triangular E (N+1)
  have he := congrArg principal (s.inv_eq E (N+1))
  rw [principal_variation _ _ _ _ _ _ (s.lower_L _) (s.upper_U _) ht.1 ht.2.1 ht.2.2,
    s.L_coherent, s.U_coherent] at he
  change variation (s.L N) (Matrix.diagonal (fun i => s.d i.val)) (s.U N)
    (principal (s.invX E (N+1))) (principal (s.invZ E (N+1)))
    (principal (s.invY E (N+1))) = fullSection E N at he
  have hu := variation_unique (s.L N) (s.Li N) (s.U N) (s.Ui N)
    (principal (s.invX E (N+1))) (principal (s.invZ E (N+1)))
    (principal (s.invY E (N+1))) (fun i => s.d i.val)
    (s.Li_L N) (s.L_Li N) (s.U_Ui N) (s.Ui_U N) (fun i => s.d_ne i.val)
    (s.lower_Li N) (s.upper_Ui N) (principal_strictLower ht.1)
    (principal_diag ht.2.1) (principal_strictUpper ht.2.2)
  dsimp only at hu
  rw [he] at hu
  exact hu

end SectionData

def coherentEntry (M : (N : ℕ) → Mat N) (i j : ℕ) : ℝ :=
  M (max i j+1) ⟨i, by omega⟩ ⟨j, by omega⟩

theorem coherent_entry_le (M : (N : ℕ) → Mat N)
    (hM : ∀ N, principal (M (N+1)) = M N)
    {m n i j : ℕ} (hmn : m≤n) (hi : i<m) (hj : j<m) :
    M m ⟨i,hi⟩ ⟨j,hj⟩ = M n ⟨i,by omega⟩ ⟨j,by omega⟩ := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hm : m=n+1
    · subst m; rfl
    · have hm' : m≤n := by omega
      have h := ih hm'
      rw [← hM n] at h
      exact h

theorem coherentEntry_section (M : (N : ℕ) → Mat N)
    (hM : ∀ N, principal (M (N+1)) = M N) (N : ℕ) (i j : Fin N) :
    coherentEntry M i.val j.val = M N i j := by
  apply coherent_entry_le M hM
  exact max_lt_iff.mpr ⟨i.isLt,j.isLt⟩

theorem coherentEntry_bound (M : (N : ℕ) → Mat N) {C : ℝ}
    (hM : ∀ N i j, |M N i j| ≤ C) (i j : ℕ) : |coherentEntry M i j| ≤ C :=
  hM _ _ _

end BTP.Stability.BandLDU
