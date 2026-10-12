import SemiInfiniteBasic
import ToeplitzSymbol

/-! Removing a finite initial block from a triangular Toeplitz product.
This is an exact identity, not a compactness or limiting argument. -/

open Finset Matrix
noncomputable section
namespace BTP

def shiftEntries (a : Entries) (s : ℕ) : Entries := fun j n => a j (n+s)

theorem entry_shift (a : Entries) (s p n r : ℕ) (hr : r ≤ n) :
    entry (shiftEntries a s) p n r = entry a p (n+s) r := by
  induction p generalizing n r with
  | zero => rfl
  | succ p ih =>
    cases r with
    | zero => simp
    | succ r =>
      have hn : 0 < n := by omega
      simp only [entry, shiftEntries]
      rw [ih n (r+1) hr, ih (n-1) r (by omega)]
      rw [show n - 1 + s = n + s - 1 by omega]

theorem shifted_product_entries (a : Entries) (s p n j : ℕ) :
    Extraction.productEntries (shiftEntries a s) p n j =
      Extraction.productEntries a p (n+s) (j+s) := by
  unfold Extraction.productEntries
  by_cases h : j ≤ n
  · rw [ite_eq_left h, ite_eq_left (by omega), entry_shift _ _ _ _ _ (by omega)]
    congr 1
    omega
  · rw [ite_eq_right h, ite_eq_right (by omega)]

/-- For a Toeplitz product, shifting every factor leaves the product unchanged. -/
theorem shifted_same_product {a : Entries} {p : ℕ}
    (ht : ∀ n j s, Extraction.productEntries a p (n+s) (j+s) =
      Extraction.productEntries a p n j) (s : ℕ) :
    SemiInfinite.SameProduct p (shiftEntries a s) a := by
  rw [SemiInfinite.sameProduct_iff_entries]
  funext n j
  exact (shifted_product_entries a s p n j).trans (ht n j s)

/-- A shift by the bandwidth removes every initial zero in Metelmann's factors. -/
theorem shifted_metelmann_positive {p : ℕ} {a : Entries}
    (ha : SemiInfinite.Metelmann p a) :
    SemiInfinite.Positive p (shiftEntries a p) := by
  intro j hj n hn
  exact ha.2 j hj (n+p) (by omega)

/-- Exact global PBF of a triangular Toeplitz product, obtained without ASW. -/
theorem triangular_toeplitz_PBF_of_metelmann {p : ℕ} {a : Entries}
    (ha : SemiInfinite.Metelmann p a)
    (ht : ∀ n j s, Extraction.productEntries a p (n+s) (j+s) =
      Extraction.productEntries a p n j) : SemiInfinite.HasPBF p a :=
  ⟨shiftEntries a p, shifted_metelmann_positive ha, shifted_same_product ht p⟩

theorem entry_one (a : Entries) (p n : ℕ) :
    entry a p n 1 = ∑ j ∈ range p, a j n := by
  simpa using entry_row a p n 0

theorem entry_nonneg {a : Entries} {p n r : ℕ} (hr : r ≤ n)
    (ha : ∀ j < p, ∀ t, 0 < t → t ≤ n → 0 ≤ a j t) :
    0 ≤ entry a p n r := by
  induction p generalizing n r with
  | zero => simp [entry]; split_ifs <;> norm_num
  | succ p ih =>
    cases r with
    | zero => simp
    | succ r =>
      rw [entry]
      exact add_nonneg (ih hr (fun j hj t ht htn => ha j (by omega) t ht htn))
        (mul_nonneg (ha p (by omega) n (by omega) le_rfl)
          (ih (by omega) (fun j hj t ht htn => ha j (by omega) t ht (by omega))))

theorem factor_le_first_subdiagonal {a : Entries} {p j n : ℕ}
    (hj : j < p) (hn : 0 < n) (ha : SemiInfinite.Metelmann p a) :
    a j n ≤ entry a p n 1 := by
  rw [entry_one]
  apply Finset.single_le_sum (f := fun i => a i n) (a := j)
  · intro i hi
    have hip := mem_range.mp hi
    by_cases hin : n ≤ i
    · rw [ha.1 i hip n hn hin]
    · exact (ha.2 i hip n (by omega)).le
  · exact mem_range.mpr hj

#print axioms triangular_toeplitz_PBF_of_metelmann

theorem extreme_entry_bound {a : Entries} {p n : ℕ} {U : ℝ} (hpn : p ≤ n)
    (hU : 0 ≤ U) (ha : ∀ j < p, ∀ t, 0 < t → t ≤ n → 0 ≤ a j t ∧ a j t ≤ U) :
    0 ≤ entry a p n p ∧ entry a p n p ≤ U^p := by
  induction p generalizing n with
  | zero => simp [entry]
  | succ p ih =>
    rw [entry_diag_step]
    have hprev := ih (n := n-1) (by omega) (fun j hj t ht htn => ha j (by omega) t ht (by omega))
    have htop := ha p (by omega) n (by omega) le_rfl
    refine ⟨mul_nonneg htop.1 hprev.1, ?_⟩
    calc
      a p n * entry a p (n-1) p ≤ U * U^p := mul_le_mul htop.2 hprev.2 hprev.1 hU
      _ = U^(p+1) := by ring

theorem extreme_entry_single_bound {a : Entries} {p n j : ℕ} {U : ℝ}
    (hj : j < p) (hpn : p ≤ n) (hU : 0 ≤ U)
    (ha : ∀ i < p, ∀ t, 0 < t → t ≤ n → 0 ≤ a i t ∧ a i t ≤ U) :
    entry a p n p ≤ U^(p-1) * a j (n-(p-1-j)) := by
  induction p generalizing n with
  | zero => omega
  | succ p ih =>
    rw [entry_diag_step]
    have hprev := extreme_entry_bound (a := a) (p := p) (n := n-1) (by omega) hU
      (fun i hi t ht htn => ha i (by omega) t ht (by omega))
    have htop := ha p (by omega) n (by omega) le_rfl
    by_cases hjp : j = p
    · subst j
      simp only [Nat.add_sub_cancel, Nat.sub_self, Nat.sub_zero]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hprev.2 htop.1
    · have hj' : j < p := by omega
      have hh := ih hj' (n := n-1) (by omega)
        (fun i hi t ht htn => ha i (by omega) t ht (by omega))
      have ht := ha j (by omega) (n-(p-j)) (by omega) (by omega)
      rw [show n-1-(p-1-j) = n-(p-j) by omega] at hh
      calc
        a p n * entry a p (n-1) p ≤ U * (U^(p-1) * a j (n-(p-j))) :=
          mul_le_mul htop.2 hh hprev.1 hU
        _ = U^p * a j (n-(p-j)) := by rw [← mul_assoc, ← pow_succ', show p-1+1=p by omega]
        _ = _ := by simp

theorem toeplitz_entry_constant {a : Entries} {p : ℕ}
    (ht : ∀ n j s, Extraction.productEntries a p (n+s) (j+s) =
      Extraction.productEntries a p n j) {n r : ℕ} (hr : r ≤ n) :
    entry a p n r = entry a p r r := by
  have h := ht r 0 (n-r)
  simpa only [Extraction.productEntries, Nat.zero_add, show r+(n-r)=n by omega,
    ite_eq_left (show n-r ≤ n by omega), ite_eq_left (show 0 ≤ r by omega),
    show n-(n-r)=r by omega, Nat.sub_zero] using h

theorem shifted_metelmann_bounded {p : ℕ} (hp : 0 < p) {a : Entries}
    (ha : SemiInfinite.Metelmann p a)
    (ht : ∀ n j s, Extraction.productEntries a p (n+s) (j+s) =
      Extraction.productEntries a p n j) {j : ℕ} (hj : j < p) :
    Toeplitz.BoundedPositive (shiftEntries a p j) := by
  let U := entry a p 1 1
  let V := entry a p p p
  have hnonneg : ∀ i < p, ∀ n, 0 < n → 0 ≤ a i n := by
    intro i hi n hn
    by_cases hni : n ≤ i
    · rw [ha.1 i hi n hn hni]
    · exact (ha.2 i hi n (by omega)).le
  have hu : ∀ i < p, ∀ n, 0 < n → a i n ≤ U := by
    intro i hi n hn
    have h := factor_le_first_subdiagonal hi hn ha
    rw [toeplitz_entry_constant ht (by omega)] at h
    exact h
  have hU : 0 < U := (ha.2 0 hp 1 (by omega)).trans_le (hu 0 hp 1 (by omega))
  have hV : 0 < V := entry_diag_pos a p p le_rfl
    (fun i hi n _ hin => ha.2 i hi n hin)
  refine ⟨V / U^(p-1), U, div_pos hV (pow_pos hU _), ?_⟩
  intro n
  refine ⟨?_, hu j hj (n+p) (by omega)⟩
  have he := extreme_entry_single_bound (a := a) (p := p) (n := n+p+(p-1-j))
    hj (by omega) hU.le (fun i hi t ht' _ => ⟨hnonneg i hi t ht', hu i hi t ht'⟩)
  rw [toeplitz_entry_constant ht (by omega), show n+p+(p-1-j)-(p-1-j)=n+p by omega] at he
  change V / U^(p-1) ≤ a j (n+p)
  exact (div_le_iff₀ (pow_pos hU _)).mpr (by simpa only [mul_comm] using he)

#print axioms shifted_metelmann_bounded
end BTP
