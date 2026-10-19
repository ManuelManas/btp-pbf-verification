import AdjacentRatios

/-! # Uniform bounds, independent of the row index -/
open Matrix Finset
noncomputable section
namespace BTP.SemiInfinite

private theorem qTail_nonneg {p : ℕ} {a : Entries} (ha : Metelmann p a)
    (l n j : ℕ) : 0 ≤ qTail a p l n j := by
  let d := max n j + 1
  unfold qTail
  rw [← inverseEntries_finite d (p - l) (fun i t => a (i + l) t)
    ⟨n, by dsimp [d]; omega⟩ ⟨j, by dsimp [d]; omega⟩]
  apply InverseBounds.qProduct_nonnegative
  intro i hi t ht htd
  exact (ha.finite d).nonnegative (i + l) (by omega) t ht htd

theorem normalizedTail_nonneg {p : ℕ} {a : Entries} (ha : Metelmann p a)
    {l : ℕ} (hl : l < p) (n j : ℕ) : 0 ≤ normalizedTail a p l n j := by
  exact div_nonneg (qTail_nonneg ha l n j) (cumulative_pos ha hl n).le

theorem normalizedTail_succ_row {p : ℕ} {a : Entries} (ha : Metelmann p a)
    {l : ℕ} (hl : l + 1 < p) {n : ℕ} (hn : l ≤ n) (j : ℕ) :
    normalizedTail a p l (n + 1) j = normalizedTail a p l n j +
      ratioAt a (l + 1) (n + 1) * normalizedTail a p (l + 1) (n + 1) j := by
  unfold normalizedTail ratioAt
  rw [qTail_succ_row _ _ _ _ _ (by omega)]
  simp only [Nat.add_sub_cancel, cumulative_succ a l n hn]
  have hc := (cumulative_pos ha (show l < p by omega) n).ne'
  have hc' := (cumulative_pos ha hl (n + 1)).ne'
  have ha0 := (ha.2 l (by omega) (n + 1) (by omega)).ne'
  field_simp
  ring

theorem normalizedTail_sum {p : ℕ} {a : Entries} (ha : Metelmann p a)
    {l j : ℕ} (hlj : l < j) (hj : j < p) {n : ℕ} (hn : l ≤ n) :
    normalizedTail a p l n j =
      ∑ s ∈ Ico (l + 1) (n + 1),
        ratioAt a (l + 1) s * normalizedTail a p (l + 1) s j := by
  induction n, hn using Nat.le_induction with
  | base =>
    simp only [normalizedTail, qTail, inverseEntries_upper _ _ _ _ hlj, zero_div,
      Ico_self, sum_empty]
  | succ n hn ih =>
    rw [normalizedTail_succ_row ha (by omega) hn j, ih,
      sum_Ico_succ_top (show l + 1 ≤ n + 1 by omega)]

private theorem ratioAt_sum_le {p : ℕ} {a : Entries} (ha : Metelmann p a)
    {k : ℕ} (hk : 0 < k) (hkp : k < p) (hs : Summable (adjacentTerm a k)) (n : ℕ) :
    (∑ s ∈ Ico k (n + 1), ratioAt a k s) ≤ ∑' t, adjacentTerm a k t := by
  rw [sum_Ico_eq_sum_range]
  change (∑ s ∈ range (n + 1 - k), adjacentTerm a k s) ≤ _
  exact Summable.sum_le_tsum _ (fun i _ => (adjacentTerm_pos ha hk hkp i).le) hs

/-- A common bound on adjacent sums bounds every normalized tail column. -/
theorem normalizedTail_bound {p : ℕ} {a : Entries} (ha : Metelmann p a)
    (hs : ∀ k, 0 < k → k < p → Summable (adjacentTerm a k))
    {C : ℝ} (hC : 1 ≤ C)
    (hCS : ∀ k, 0 < k → k < p → (∑' n, adjacentTerm a k n) ≤ C)
    {l j n : ℕ} (hl : l < p) (hj : j < p) (hn : l ≤ n) :
    normalizedTail a p l n j ≤ C ^ (p - l) := by
  have hpow : ∀ d l, p - l = d → l < p → ∀ j, j < p → ∀ n, l ≤ n →
      normalizedTail a p l n j ≤ C ^ d := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro l hdl hl j hj n hn
      by_cases hjl : j < l
      · rw [normalizedTail_before ha hjl hn]
        exact pow_nonneg (by linarith) _
      · by_cases heq : j = l
        · subst j
          rw [normalizedTail_diagonal ha hl hn]
          exact one_le_pow₀ hC
        · have hlj : l < j := by omega
          have hlp : l + 1 < p := by omega
          have hr : p - (l + 1) < d := by omega
          rw [normalizedTail_sum ha hlj hj hn]
          calc
            _ ≤ ∑ s ∈ Ico (l + 1) (n + 1), ratioAt a (l + 1) s * C ^ (p - (l + 1)) := by
              apply sum_le_sum
              intro s hs'
              apply mul_le_mul_of_nonneg_left
                (ih (p - (l + 1)) hr (l + 1) rfl hlp j hj s (mem_Ico.mp hs').1)
              exact (div_pos (cumulative_pos ha hlp s) (cumulative_pos ha (by omega) s)).le
            _ = (∑ s ∈ Ico (l + 1) (n + 1), ratioAt a (l + 1) s) * C ^ (p - (l + 1)) := by
              rw [sum_mul]
            _ ≤ C * C ^ (p - (l + 1)) :=
              mul_le_mul_of_nonneg_right
                ((ratioAt_sum_le ha (by omega) hlp (hs _ (by omega) hlp) n).trans
                  (hCS _ (by omega) hlp)) (pow_nonneg (by linarith) _)
            _ = C ^ d := by
              rw [show d = p - (l + 1) + 1 by omega, pow_succ]
              ring
  exact hpow (p - l) l rfl hl j hj n hn

/-- A determinant of order k has k! summands, each bounded by B^k. -/
theorem abs_det_le_factorial {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ)
    {B : ℝ} (_hB : 0 ≤ B) (hM : ∀ i j, |M i j| ≤ B) :
    |M.det| ≤ (Nat.factorial k : ℝ) * B ^ k := by
  rw [Matrix.det_apply]
  calc
    _ ≤ ∑ σ : Equiv.Perm (Fin k), |σ.sign • ∏ i, M (σ i) i| := abs_sum_le_sum_abs _ _
    _ = ∑ σ : Equiv.Perm (Fin k), ∏ i, |M (σ i) i| := by
      apply sum_congr rfl
      intro σ _
      simp [Units.smul_def, zsmul_eq_mul, abs_mul, ← Int.cast_abs, Equiv.Perm.sign_abs, abs_prod]
    _ ≤ ∑ _σ : Equiv.Perm (Fin k), B ^ k := by
      apply sum_le_sum
      intro σ _
      calc
        _ ≤ ∏ _i : Fin k, B := prod_le_prod (fun _ _ => abs_nonneg _) (fun i _ => hM (σ i) i)
        _ = B ^ k := by simp
    _ = _ := by simp [Fintype.card_perm, nsmul_eq_mul]

/-- Actual inverse minors have a uniform bound once the adjacent series converge.
The constant need not be optimal; its independence of n is the relevant fact. -/
theorem uniform_inverse_minors {p : ℕ} {a : Entries} (ha : Metelmann p a)
    (hs : ∀ k, 0 < k → k < p → Summable (adjacentTerm a k)) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ k, k ≤ p → ∀ n, ∀ c : Fin k → ℕ,
      (∀ j, c j < p) →
      |consecutiveMinor a p k n c / consecutiveMinor a p k n (fun j => j.val)| ≤
        (Nat.factorial k : ℝ) * B ^ k := by
  let S : Fin (p - 1) → ℝ := fun i => ∑' n, adjacentTerm a (i.val + 1) n
  have hS : ∀ i, 0 ≤ S i := by
    intro i
    exact ((hs _ (by omega) (by omega)).tsum_pos
      (fun n => (adjacentTerm_pos ha (by omega) (by omega) n).le) 0
      (adjacentTerm_pos ha (by omega) (by omega) 0)).le
  let C := 1 + ∑ i, S i
  have hC : 1 ≤ C := by dsimp [C]; exact le_add_of_nonneg_right (sum_nonneg fun i _ => hS i)
  have hCS : ∀ k, 0 < k → k < p → (∑' n, adjacentTerm a k n) ≤ C := by
    intro k hk hkp
    let i : Fin (p - 1) := ⟨k - 1, by omega⟩
    have hi : i.val + 1 = k := by dsimp [i]; omega
    have hle := single_le_sum (fun j (_ : j ∈ (univ : Finset (Fin (p - 1)))) => hS j) (mem_univ i)
    have heq : S i = ∑' n, adjacentTerm a k n := by simp only [S, hi]
    rw [heq] at hle
    dsimp [C]
    linarith
  refine ⟨C ^ p, one_le_pow₀ hC, ?_⟩
  intro k hk n c hc
  rw [normalized_minor_identity ha hk]
  apply abs_det_le_factorial _ (pow_nonneg (by linarith) _)
  intro i j
  rw [Matrix.of_apply, abs_of_nonneg (normalizedTail_nonneg ha (by omega) _ _)]
  exact (normalizedTail_bound ha hs hC hCS (by omega) (hc j) (by omega)).trans
    (pow_le_pow_right₀ hC (Nat.sub_le p i.val))

#print axioms uniform_inverse_minors
end BTP.SemiInfinite
