import SemiInfiniteBasic

/-! # The triangular signed inverse on the half-line

All sums and recurrences are finite. No bounded operator inverse is used.
The comparison theorem identifies this definition with J L_d⁻¹ J in EVERY
large enough section; it is not an abstract auxiliary positive matrix.
-/

open Matrix Finset Filter
open scoped Topology
noncomputable section
namespace BTP.SemiInfinite
open InverseBounds

def inverseEntries (a : Entries) : ℕ → ℕ → ℕ → ℝ
  | 0, n, j => if n = j then 1 else 0
  | p + 1, n, j => Nat.rec (if 0 = j then 1 else 0)
      (fun t x => inverseEntries (fun i m => a (i + 1) m) p (t + 1) j + a 0 (t + 1) * x) n

@[simp] theorem inverseEntries_zero_row (a : Entries) (p j : ℕ) :
    inverseEntries a p 0 j = if 0 = j then 1 else 0 := by
  cases p <;> rfl

@[simp] theorem inverseEntries_succ (a : Entries) (p n j : ℕ) :
    inverseEntries a (p + 1) (n + 1) j =
      inverseEntries (fun i m => a (i + 1) m) p (n + 1) j +
        a 0 (n + 1) * inverseEntries a (p + 1) n j := rfl

theorem inverseEntries_finite (d p : ℕ) (a : Entries) (i j : Fin d) :
    qProduct d a p i j = inverseEntries a p i.val j.val := by
  induction p generalizing a i j with
  | zero => simp [qProduct, inverseEntries, Matrix.one_apply, Fin.ext_iff]
  | succ p ih =>
    have hrow := first_row_equation d a p
    induction hn : i.val generalizing i with
    | zero =>
      have h := congrArg (fun M : Square d => M i j) hrow
      rw [bidiagonal_mul_zero _ _ _ _ hn, ih] at h
      simpa [hn] using h
    | succ n ihn =>
      let prev : Fin d := ⟨n, by omega⟩
      have hprev : (⟨i.val - 1, by omega⟩ : Fin d) = prev := by
        apply Fin.ext; dsimp [prev]; omega
      have h := congrArg (fun M : Square d => M i j) hrow
      rw [bidiagonal_mul_pos _ _ _ _ (by omega), hprev, ih, ihn prev rfl] at h
      rw [inverseEntries_succ]
      rw [hn] at h
      linarith

theorem signed_inverse_section (d p : ℕ) (a : Entries) (i j : Fin d) :
    inverseEntries a p i j = checker ((lowerProduct d a p)⁻¹) i j := by
  rw [← inverseEntries_finite, qProduct_signed_inverse]

/-- Increasing a truncation does not change any of these inverse entries. -/
theorem inverse_compatible {d D p : ℕ} (a : Entries) (h : d ≤ D) (i j : Fin d) :
    checker ((lowerProduct D a p)⁻¹) (Fin.castLE h i) (Fin.castLE h j) =
      checker ((lowerProduct d a p)⁻¹) i j := by
  rw [← signed_inverse_section, ← signed_inverse_section]
  rfl

theorem inverseEntries_upper (a : Entries) (p n j : ℕ) (h : n < j) :
    inverseEntries a p n j = 0 := by
  induction p generalizing a n j with
  | zero => simp [inverseEntries, Nat.ne_of_lt h]
  | succ p ih =>
    induction n with
    | zero => simp [show 0 ≠ j by omega]
    | succ n ihn =>
      rw [inverseEntries_succ, ih _ _ _ h, ihn (by omega)]
      ring

theorem inverseEntries_diagonal (a : Entries) (p n : ℕ) :
    inverseEntries a p n n = 1 := by
  induction p generalizing a n with
  | zero => simp [inverseEntries]
  | succ p ih =>
    cases n with
    | zero => simp
    | succ n => rw [inverseEntries_succ, ih, inverseEntries_upper a (p + 1) n (n + 1) (by omega)]; ring

theorem inverseEntries_pos {p : ℕ} {a : Entries} (hp : 0 < p)
    (ha : SemiInfinite.Metelmann p a) {n j : ℕ} (hjn : j ≤ n) :
    0 < inverseEntries a p n j := by
  rw [← inverseEntries_finite (n + 1) p a ⟨n, by omega⟩ ⟨j, by omega⟩]
  exact metelmann_inverse_pos a hp (ha.finite _) _ _ hjn

/-- The order-one ratio, with the manuscript's row number equal to n+1. -/
def inverseEntryRatio (a : Entries) (p n : ℕ) : ℝ :=
  inverseEntries a p (n + 1) 0 / inverseEntries a p (n + 1) 1

theorem inverseEntryRatio_pos {p : ℕ} {a : Entries} (hp : 0 < p)
    (ha : SemiInfinite.Metelmann p a) (n : ℕ) : 0 < inverseEntryRatio a p n := by
  exact div_pos (inverseEntries_pos hp ha (by omega)) (inverseEntries_pos hp ha (by omega))

theorem inverseEntryRatio_strictAnti {p : ℕ} {a : Entries} (hp : 2 ≤ p)
    (ha : SemiInfinite.Metelmann p a) : StrictAnti (inverseEntryRatio a p) := by
  apply strictAnti_nat_of_succ_lt
  intro n
  have h := (kappa_strictly_decreasing (d := n + 3) (by omega) a hp (ha.finite _)
    ⟨n + 1, by omega⟩ ⟨n + 2, by omega⟩ (by dsimp; omega) rfl).1
  simpa only [kappa, inverseEntries_finite, inverseEntryRatio] using h

def inverseEntryLimit (a : Entries) (p : ℕ) : ℝ := ⨅ n, inverseEntryRatio a p n

theorem inverseEntryRatio_tendsto {p : ℕ} {a : Entries} (hp : 2 ≤ p)
    (ha : SemiInfinite.Metelmann p a) :
    Tendsto (inverseEntryRatio a p) atTop (𝓝 (inverseEntryLimit a p)) := by
  apply tendsto_atTop_ciInf (inverseEntryRatio_strictAnti hp ha).antitone
  refine ⟨0, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact (inverseEntryRatio_pos (by omega) ha n).le

/-- A global factorization gives a fixed, strictly positive bound for the limit.
The finite proposition alone did not exchange the two quantifiers. -/
theorem global_first_limit_positive {p : ℕ} {a : Entries} (hp : 2 ≤ p)
    (ha : SemiInfinite.Metelmann p a) (hP : HasPBF p a) :
    0 < inverseEntryLimit a p := by
  obtain ⟨b, hb, heq⟩ := hP
  have hbound : ∀ n, b (p - 1) 1 < inverseEntryRatio a p n := by
    intro n
    have h := (positive_refactorization_bound (d := n + 2) (by omega) a b hp
      (ha.finite _) (hb.finite _) (heq _) ⟨n + 1, by omega⟩ (by dsimp; omega)).2
    simpa only [kappa, inverseEntries_finite, inverseEntryRatio] using h
  exact lt_of_lt_of_le (hb (p - 1) (by omega) 1 (by omega))
    (le_ciInf (fun n => (hbound n).le))

#print axioms signed_inverse_section
#print axioms inverse_compatible
#print axioms global_first_limit_positive
end BTP.SemiInfinite
