import PrefixBounds

/-! # Necessity of every inverse-minor limit -/
open Matrix Finset Filter
noncomputable section
namespace BTP.SemiInfinite
open Extraction InverseBounds

/-- The two constants come from a fixed finite prefix of the global factors.
Adding the remaining inverse factors preserves all the required inequalities. -/
theorem positive_product_uniform_bound (p k : ℕ) (hp : k + 1 ≤ p)
    (b : Entries) (hb : Positive p b) :
    ∃ α β : ℝ, 0 < α ∧ 0 < β ∧
      RowNonnegative (weightedBoundary (inverseEntries b p) k α β) := by
  induction p using Nat.strong_induction_on generalizing b with
  | h p ih =>
    by_cases he : p = k + 1
    · subst p
      refine ⟨productEntries b (k + 1) k 0, productEntries b (k + 1) (k + 1) 0,
        ?_, ?_, inverse_prefix_weighted_nonnegative b k hb⟩
      · simp only [productEntries, Nat.zero_le, ite_true, Nat.sub_zero]
        exact positive_entry_positive hb k k le_rfl (by omega)
      · simp only [productEntries, Nat.zero_le, ite_true, Nat.sub_zero]
        exact positive_entry_positive hb (k + 1) (k + 1) le_rfl le_rfl
    · have hp' : k + 1 ≤ p - 1 := by omega
      obtain ⟨α, β, hα, hβ, hM⟩ := ih (p - 1) (by omega) hp'
        (fun i n => b (i + 1) n) (fun i hi n hn => hb (i + 1) (by omega) n hn)
      refine ⟨α, β, hα, hβ, ?_⟩
      apply rowNonnegative_forward
        (weightedBoundary (inverseEntries (fun i n => b (i + 1) n) (p - 1)) k α β)
        (weightedBoundary (inverseEntries b p) k α β) (b 0) hM
      · intro n hn; exact (hb 0 (by omega) n hn).le
      · funext j
        simp only [weightedBoundary, inverseEntries_zero_row]
      · intro n; funext j
        rw [show p = (p - 1) + 1 by omega]
        simp only [weightedBoundary, inverseEntries_succ, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Nat.add_sub_cancel]
        split_ifs <;> ring

theorem sameProduct_inverseEntries {p : ℕ} {a b : Entries} (he : SameProduct p a b) :
    inverseEntries a p = inverseEntries b p := by
  funext n j
  let d := max n j + 1
  have hn : n < d := by dsimp [d]; omega
  have hj : j < d := by dsimp [d]; omega
  change inverseEntries a p (⟨n, hn⟩ : Fin d).val (⟨j, hj⟩ : Fin d).val = _
  rw [signed_inverse_section, he d, ← signed_inverse_section]

/-- A global PBF forces every one of the p-1 limits to be strictly positive. -/
theorem PBF_gives_positive_limits {p : ℕ} {a : Entries} (ha : Metelmann p a)
    (hP : HasPBF p a) (k : ℕ) (hk : k + 1 < p) :
    0 < inverseMinorLimit a p k := by
  obtain ⟨b, hb, he⟩ := hP
  obtain ⟨α, β, hα, hβ, hbound⟩ := positive_product_uniform_bound p k (by omega) b hb
  rw [sameProduct_inverseEntries he] at hbound
  have hle : ∀ n, β / α ≤ inverseMinorRatio a p k n := by
    intro n
    have hminor := hbound (fun i : Fin (k + 1) => n + 1 + i.val)
      (by intro i j hij; change i.val < j.val at hij; change n + 1 + i.val < n + 1 + j.val; omega)
    rw [weightedBoundary_det] at hminor
    have hnum := leading_minor_pos ha (show k + 1 ≤ p by omega) (n + 1)
    have hratio : 0 < inverseMinorRatio a p k n := by
      rw [inverseMinorRatio_eq_convergent ha hk]
      exact convergent_pos (adjacentTerm_pos ha (by omega) hk) n
    unfold inverseMinorRatio at hratio ⊢
    have hden := (div_pos_iff_of_pos_left hnum).mp hratio
    apply (div_le_div_iff₀ hα hden).mpr
    change 0 ≤ α * consecutiveMinor a p (k + 1) (n + 1) (fun j => j.val) -
      β * consecutiveMinor a p (k + 1) (n + 1) (nextColumns k) at hminor
    linarith
  exact lt_of_lt_of_le (div_pos hβ hα) (le_ciInf hle)

theorem PBF_iff_positive_limits {p : ℕ} (hp : 0 < p) {a : Entries}
    (ha : Metelmann p a) :
    HasPBF p a ↔ ∀ k, k + 1 < p → 0 < inverseMinorLimit a p k := by
  exact ⟨fun h k hk => PBF_gives_positive_limits ha h k hk, positive_limits_give_PBF hp ha⟩

theorem PBF_iff_summable_series {p : ℕ} (hp : 0 < p) {a : Entries}
    (ha : Metelmann p a) :
    HasPBF p a ↔ ∀ k, 0 < k → k < p → Summable (adjacentTerm a k) := by
  constructor
  · intro h k hk hkp
    apply (seriesEndpoint_pos_iff ha hk hkp).mp
    have he := PBF_gives_positive_limits ha h (k - 1) (by omega)
    rw [inverseMinorLimit_eq_seriesEndpoint ha (by omega), show k - 1 + 1 = k by omega] at he
    exact he
  · exact summable_series_give_PBF hp ha

#print axioms PBF_gives_positive_limits
#print axioms PBF_iff_positive_limits
end BTP.SemiInfinite
