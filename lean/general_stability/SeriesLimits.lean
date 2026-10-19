import Proposition215

/-!
# Limits of the adjacent positive series

The index `n` in `convergent r n` is the manuscript's `N-1`.
No inverse-minor identity or factorization theorem is assumed here.
Those matrix statements are separate obligations.
-/

open Filter Finset
open scoped Topology
noncomputable section
namespace BTP.SemiInfinite

/-- The nonempty partialSum sum, with exactly `n+1` terms. -/
def partialSum (r : ℕ → ℝ) (n : ℕ) : ℝ := ∑ j ∈ range (n + 1), r j

/-- Reciprocal of a nonempty partialSum sum. -/
def convergent (r : ℕ → ℝ) (n : ℕ) : ℝ := (partialSum r n)⁻¹

/-- The infimum exists because the convergents are positive. -/
def endpoint (r : ℕ → ℝ) : ℝ := ⨅ n, convergent r n

theorem partial_pos {r : ℕ → ℝ} (hr : ∀ n, 0 < r n) (n : ℕ) :
    0 < partialSum r n := by
  apply sum_pos
  · intro j _; exact hr j
  · exact ⟨0, by simp⟩

theorem convergent_pos {r : ℕ → ℝ} (hr : ∀ n, 0 < r n) (n : ℕ) :
    0 < convergent r n := inv_pos.mpr (partial_pos hr n)

theorem partial_succ (r : ℕ → ℝ) (n : ℕ) :
    partialSum r (n + 1) = partialSum r n + r (n + 1) := by
  simp [partialSum, sum_range_succ]

theorem convergent_strictAnti {r : ℕ → ℝ} (hr : ∀ n, 0 < r n) :
    StrictAnti (convergent r) := by
  apply strictAnti_nat_of_succ_lt
  intro n
  change (partialSum r (n + 1))⁻¹ < (partialSum r n)⁻¹
  apply inv_strictAnti₀ (partial_pos hr n)
  rw [partial_succ]
  exact lt_add_of_pos_right _ (hr (n + 1))

theorem convergent_bddBelow {r : ℕ → ℝ} (hr : ∀ n, 0 < r n) :
    BddBelow (Set.range (convergent r)) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact (convergent_pos hr n).le

theorem endpoint_nonneg {r : ℕ → ℝ} (hr : ∀ n, 0 < r n) :
    0 ≤ endpoint r := by
  exact le_ciInf (fun n => (convergent_pos hr n).le)

theorem endpoint_le {r : ℕ → ℝ} (hr : ∀ n, 0 < r n) (n : ℕ) :
    endpoint r ≤ convergent r n := ciInf_le (convergent_bddBelow hr) n

theorem convergent_tendsto {r : ℕ → ℝ} (hr : ∀ n, 0 < r n) :
    Tendsto (convergent r) atTop (𝓝 (endpoint r)) :=
  tendsto_atTop_ciInf (convergent_strictAnti hr).antitone (convergent_bddBelow hr)

theorem endpoint_lt {r : ℕ → ℝ} (hr : ∀ n, 0 < r n) (n : ℕ) :
    endpoint r < convergent r n :=
  lt_of_le_of_lt (endpoint_le hr (n + 1)) (convergent_strictAnti hr (by omega))

theorem endpoint_eq_inv_tsum {r : ℕ → ℝ} (hr : ∀ n, 0 < r n)
    (hs : Summable r) : endpoint r = (∑' n, r n)⁻¹ := by
  have hsum : 0 < ∑' n, r n := hs.tsum_pos (fun n => (hr n).le) 0 (hr 0)
  have hpartial : Tendsto (partialSum r) atTop (𝓝 (∑' n, r n)) := by
    exact hs.hasSum.tendsto_sum_nat.comp (by exact Filter.tendsto_atTop_mono (fun n => Nat.le_add_right n 1) tendsto_id)
  exact tendsto_nhds_unique (convergent_tendsto hr)
    ((tendsto_inv₀ hsum.ne').comp hpartial)

theorem endpoint_pos_iff_summable {r : ℕ → ℝ} (hr : ∀ n, 0 < r n) :
    0 < endpoint r ↔ Summable r := by
  constructor
  · intro he
    apply summable_of_sum_range_le (fun n => (hr n).le) (c := (endpoint r)⁻¹)
    intro n
    cases n with
    | zero => simpa using (inv_pos.mpr he).le
    | succ n =>
      have h := inv_anti₀ he (endpoint_le hr n)
      simpa [convergent, partialSum] using h
  · intro hs
    rw [endpoint_eq_inv_tsum hr hs]
    apply inv_pos.mpr
    exact hs.tsum_pos (fun n => (hr n).le) 0 (hr 0)

theorem endpoint_eq_zero_iff_not_summable {r : ℕ → ℝ} (hr : ∀ n, 0 < r n) :
    endpoint r = 0 ↔ ¬ Summable r := by
  rw [← endpoint_pos_iff_summable hr]
  constructor
  · intro h; rw [h]; exact lt_irrefl 0
  · intro h; exact le_antisymm (le_of_not_gt h) (endpoint_nonneg hr)

/-- A fixed positive parameter lies below every finite bound exactly when it
lies at or below the limiting bound. The endpoint is allowed. -/
theorem admissible_parameter_iff {r : ℕ → ℝ} (hr : ∀ n, 0 < r n) (u : ℝ) :
    (∀ n, u < convergent r n) ↔ u ≤ endpoint r := by
  constructor
  · intro h; exact le_ciInf (fun n => (h n).le)
  · intro h n; exact lt_of_le_of_lt h (endpoint_lt hr n)

/-- There is one coordinate for each lower or upper obstruction. -/
abbrev ObstructionIndex (p q : ℕ) := Fin (p - 1) ⊕ Fin (q - 1)

theorem number_of_limits {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    Fintype.card (ObstructionIndex p q) = p + q - 2 := by
  simp only [ObstructionIndex, Fintype.card_sum, Fintype.card_fin]
  omega

/-- Simultaneous series convergence is exactly positivity of all the limits.
This is the analytic part, not yet the positive-factorization conclusion. -/
theorem all_endpoints_pos_iff {ι : Type*} (r : ι → ℕ → ℝ)
    (hr : ∀ i n, 0 < r i n) :
    (∀ i, 0 < endpoint (r i)) ↔ ∀ i, Summable (r i) := by
  exact forall_congr' (fun i => endpoint_pos_iff_summable (hr i))

#print axioms endpoint_pos_iff_summable
#print axioms admissible_parameter_iff
#print axioms all_endpoints_pos_iff
end BTP.SemiInfinite
