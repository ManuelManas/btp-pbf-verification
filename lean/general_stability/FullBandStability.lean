import BandLDU
import WeightedShift
import InverseSections
import Mathlib.Tactic

/-! Uniform estimates for the finite sums occurring in the LDU derivative.
All combinatorial constants are independent of the finite-section size. -/
open Finset
open scoped BigOperators
noncomputable section
namespace BTP.Stability.BandLDU

/-- At fixed minimum index, a band contains at most p+q+1 pairs.
The injection records the signed diagonal difference by v+p-u. -/
theorem band_fiber_card (S : Finset (ℕ × ℕ)) (p q s : ℕ)
    (hband : ∀ uv ∈ S, uv.1 ≤ uv.2+p ∧ uv.2 ≤ uv.1+q) :
    (S.filter (fun uv => min uv.1 uv.2 = s)).card ≤ p+q+1 := by
  have hc := card_le_card_of_injOn (s := S.filter (fun uv => min uv.1 uv.2 = s))
    (t := range (p+q+1)) (fun uv : ℕ×ℕ => uv.2+p-uv.1) ?_ ?_
  · simpa using hc
  · intro uv huv
    have hmem := (mem_filter.mp huv).1
    have hb := hband uv hmem
    simp only [mem_coe, mem_range]
    omega
  · intro uv huv xy hxy he
    have hu := mem_filter.mp huv
    have hx := mem_filter.mp hxy
    have hbu := hband uv hu.1
    have hbx := hband xy hx.1
    apply Prod.ext <;> dsimp at * <;> omega

/-- Counting each minimum index once per permitted diagonal gives a bound
by the common row sum, rather than by the number of rows. -/
theorem band_sum_bound (S : Finset (ℕ×ℕ)) (p q N : ℕ)
    (g : ℕ×ℕ → ℝ) (r : ℕ → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hr : ∀ s, 0 ≤ r s)
    (hband : ∀ uv ∈ S, uv.1 ≤ uv.2+p ∧ uv.2 ≤ uv.1+q)
    (hN : ∀ uv ∈ S, min uv.1 uv.2 < N)
    (hg : ∀ uv ∈ S, g uv ≤ K*r (min uv.1 uv.2)) :
    ∑ uv ∈ S, g uv ≤ (p+q+1 : ℝ)*K*(∑ s ∈ range N, r s) := by
  have hmaps : ∀ uv ∈ S, min uv.1 uv.2 ∈ range N := by
    intro uv huv; exact mem_range.mpr (hN uv huv)
  rw [← sum_fiberwise_of_maps_to hmaps g]
  calc
    _ ≤ ∑ s ∈ range N, (p+q+1 : ℝ)*K*r s := by
      apply sum_le_sum
      intro s _
      calc
        _ ≤ ∑ uv ∈ S.filter (fun uv => min uv.1 uv.2 = s), K*r s := by
          apply sum_le_sum
          intro uv huv
          have hm := mem_filter.mp huv
          simpa only [hm.2] using hg uv hm.1
        _ = ((S.filter (fun uv => min uv.1 uv.2 = s)).card : ℝ)*(K*r s) := by simp
        _ ≤ (p+q+1 : ℝ)*K*r s := by
          have hc : ((S.filter (fun uv => min uv.1 uv.2 = s)).card : ℝ) ≤ (p+q+1 : ℝ) := by
            exact_mod_cast band_fiber_card S p q s hband
          have := mul_le_mul_of_nonneg_right hc (mul_nonneg hK (hr s))
          simpa only [mul_assoc] using this
    _ = _ := by rw [← mul_sum]

/-- Iterated neighbor comparisons in the row direction. -/
theorem row_neighbor_iterate (Q : ℕ → ℕ → ℝ) {α : ℝ} (hα : 0 ≤ α)
    (hrow : ∀ n s, s ≤ n → α*Q n s ≤ Q (n+1) s)
    (n s k : ℕ) (hs : s ≤ n) : α^k*Q n s ≤ Q (n+k) s := by
  induction k with
  | zero => simp
  | succ k ih =>
    have ht := hrow (n+k) s (by omega)
    have hm := mul_le_mul_of_nonneg_left ih hα
    calc
      α^(k+1)*Q n s = α*(α^k*Q n s) := by rw [pow_succ]; ring
      _ ≤ α*Q (n+k) s := hm
      _ ≤ Q (n+(k+1)) s := by simpa only [Nat.add_assoc] using ht

/-- Iterated neighbor comparisons in the column direction. -/
theorem col_neighbor_iterate (Q : ℕ → ℕ → ℝ) {α : ℝ} (hα : 0 ≤ α)
    (hcol : ∀ n s, s < n → α*Q n (s+1) ≤ Q n s)
    (n s k : ℕ) (hs : s+k ≤ n) : α^k*Q n (s+k) ≤ Q n s := by
  induction k generalizing s with
  | zero => simp
  | succ k ih =>
    have hk : s+1+k ≤ n := by omega
    have hi := ih (s+1) hk
    have ht := hcol n s (by omega)
    have hm := mul_le_mul_of_nonneg_left hi hα
    calc
      α^(k+1)*Q n (s+(k+1)) = α*(α^k*Q n ((s+1)+k)) := by
        rw [show s+(k+1)=(s+1)+k by omega, pow_succ]; ring
      _ ≤ α*Q n (s+1) := hm
      _ ≤ Q n s := ht

/-- Moving to a common later row and earlier column costs one inverse
power per move. This estimate applies to the actual signed inverse kernels. -/
theorem inverse_entry_compare (Q : ℕ → ℕ → ℝ) {α : ℝ} (hα : 0 < α)
    (hrow : ∀ n s, s ≤ n → α*Q n s ≤ Q (n+1) s)
    (hcol : ∀ n s, s < n → α*Q n (s+1) ≤ Q n s)
    (i u N s : ℕ) (hui : u ≤ i) (hiN : i ≤ N) (hsu : s ≤ u) :
    Q i u ≤ (α^((N-i)+(u-s)))⁻¹ * Q N s := by
  have hr := row_neighbor_iterate Q hα.le hrow i u (N-i) hui
  rw [Nat.add_sub_of_le hiN] at hr
  have hc := col_neighbor_iterate Q hα.le hcol N s (u-s) (by omega)
  rw [Nat.add_sub_of_le hsu] at hc
  have hm := mul_le_mul_of_nonneg_left hr (pow_nonneg hα.le (u-s))
  have hall : α^((N-i)+(u-s))*Q i u ≤ Q N s := by
    calc
      _ = α^(u-s)*(α^(N-i)*Q i u) := by rw [pow_add]; ring
      _ ≤ α^(u-s)*Q N u := hm
      _ ≤ Q N s := hc
  have hp : 0 < α^((N-i)+(u-s)) := pow_pos hα _
  have := (le_div_iff₀ hp).mpr (by simpa only [mul_comm] using hall)
  simpa only [div_eq_mul_inv, mul_comm] using this


/-- The two inverse entries can be compared with one common row-sum term.
The constant depends on the band, never on the row indices. -/
theorem near_inverse_product_bound (Q R : ℕ → ℕ → ℝ) {β : ℝ}
    (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hQ : ∀ n s, 0 ≤ Q n s) (hR : ∀ n s, 0 ≤ R n s)
    (hQr : ∀ n s, s ≤ n → β*Q n s ≤ Q (n+1) s)
    (hQc : ∀ n s, s < n → β*Q n (s+1) ≤ Q n s)
    (hRr : ∀ n s, s ≤ n → β*R n s ≤ R (n+1) s)
    (hRc : ∀ n s, s < n → β*R n (s+1) ≤ R n s)
    (i j u v h : ℕ) (hui : u ≤ i) (hvj : v ≤ j)
    (hij : i ≤ j+h) (hji : j ≤ i+h) (huv : u ≤ v+h) (hvu : v ≤ u+h) :
    Q i u * R j v ≤ (β⁻¹)^(2*h) *
      (Q (max i j) (min u v)*R (max i j) (min u v)) := by
  let N := max i j
  let s := min u v
  have h1 := inverse_entry_compare Q hβ hQr hQc i u N s hui (le_max_left _ _) (min_le_left _ _)
  have h2 := inverse_entry_compare R hβ hRr hRc j v N s hvj (le_max_right _ _) (min_le_right _ _)
  have hm := mul_le_mul h1 h2 (hR j v)
    (mul_nonneg (inv_nonneg.mpr (pow_nonneg hβ.le _)) (hQ N s))
  have he : ((N-i)+(u-s))+((N-j)+(v-s)) ≤ 2*h := by dsimp [N,s]; omega
  have hi : 1 ≤ β⁻¹ := (one_le_inv₀ hβ).mpr hβ1
  have hp := pow_le_pow_right₀ hi he
  calc
    _ ≤ (β^((N-i)+(u-s)))⁻¹ * Q N s * ((β^((N-j)+(v-s)))⁻¹ * R N s) := hm
    _ = (β⁻¹)^(((N-i)+(u-s))+((N-j)+(v-s))) * (Q N s*R N s) := by
      simp only [pow_add]; ring
    _ ≤ (β⁻¹)^(2*h)*(Q N s*R N s) :=
      mul_le_mul_of_nonneg_right hp (mul_nonneg (hQ N s) (hR N s))

/-- The manuscript's near-diagonal estimate from bounded joint row sums. -/
theorem near_diagonal_sum_bound (Q R : ℕ → ℕ → ℝ) {β Z : ℝ}
    (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hQ : ∀ n s, 0 ≤ Q n s) (hR : ∀ n s, 0 ≤ R n s)
    (hQr : ∀ n s, s ≤ n → β*Q n s ≤ Q (n+1) s)
    (hQc : ∀ n s, s < n → β*Q n (s+1) ≤ Q n s)
    (hRr : ∀ n s, s ≤ n → β*R n s ≤ R (n+1) s)
    (hRc : ∀ n s, s < n → β*R n (s+1) ≤ R n s)
    (hZ : ∀ n, ∑ s ∈ range (n+1), Q n s*R n s ≤ Z)
    (p q i j : ℕ) (hij : i ≤ j+max p q) (hji : j ≤ i+max p q) :
    ∑ uv ∈ ((range (i+1) ×ˢ range (j+1)).filter
      (fun uv => uv.1 ≤ uv.2+p ∧ uv.2 ≤ uv.1+q)), Q i uv.1*R j uv.2
    ≤ (p+q+1 : ℝ)*(β⁻¹)^(2*max p q)*Z := by
  let S := (range (i+1) ×ˢ range (j+1)).filter
      (fun uv => uv.1 ≤ uv.2+p ∧ uv.2 ≤ uv.1+q)
  have hband : ∀ uv ∈ S, uv.1 ≤ uv.2+p ∧ uv.2 ≤ uv.1+q := by
    intro uv huv; exact (mem_filter.mp huv).2
  have hrows : ∀ uv ∈ S, uv.1 ≤ i ∧ uv.2 ≤ j := by
    intro uv huv
    have ht := mem_product.mp (mem_filter.mp huv).1
    exact ⟨by simpa using ht.1, by simpa using ht.2⟩
  have hs : ∀ uv ∈ S, min uv.1 uv.2 < max i j+1 := by
    intro uv huv; have := hrows uv huv; omega
  have hprod : ∀ uv ∈ S, Q i uv.1*R j uv.2 ≤ (β⁻¹)^(2*max p q)*
      (Q (max i j) (min uv.1 uv.2)*R (max i j) (min uv.1 uv.2)) := by
    intro uv huv
    have hr := hrows uv huv
    have hb := hband uv huv
    exact near_inverse_product_bound Q R hβ hβ1 hQ hR hQr hQc hRr hRc
      i j uv.1 uv.2 (max p q) hr.1 hr.2 hij hji (by omega) (by omega)
  have hb := band_sum_bound S p q (max i j+1)
    (fun uv => Q i uv.1*R j uv.2) (fun s => Q (max i j) s*R (max i j) s)
    (pow_nonneg (inv_nonneg.mpr hβ.le) _) (fun s => mul_nonneg (hQ _ s) (hR _ s))
    hband hs hprod
  exact le_trans hb (mul_le_mul_of_nonneg_left (hZ _) (by positivity))

/-- Joint inverse-row bounds force the cross-weight geometric condition
as soon as each kernel dominates its last-factor product. -/
theorem cross_decay_of_inverse_row_bound (a b : ℕ → ℝ) (Q R : ℕ → ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n)
    (hQ : ∀ n s, s ≤ n → BTP.Stability.blockProduct a s (n-s) ≤ Q n s)
    (hR : ∀ n s, s ≤ n → BTP.Stability.blockProduct b s (n-s) ≤ R n s)
    {M : ℝ} (hM : ∀ n, ∑ s ∈ range (n+1), Q n s*R n s ≤ M) :
    ∃ C ρ : ℝ, 1 ≤ C ∧ 0 < ρ ∧ ρ < 1 ∧
      ∀ s N, BTP.Stability.blockProduct (fun t => a t*b t) s N ≤ C*ρ^N := by
  apply BTP.Stability.geometric_of_rowSum_bound (fun t => mul_nonneg (ha t) (hb t))
  intro n
  rw [BTP.Stability.rowSum_eq_sum]
  apply le_trans _ (hM n)
  apply sum_le_sum
  intro s hs
  have hsn : s ≤ n := by simpa using hs
  have hQa : 0 ≤ BTP.Stability.blockProduct a s (n-s) := BTP.Stability.blockProduct_nonneg ha _ _
  have hRb : 0 ≤ BTP.Stability.blockProduct b s (n-s) := BTP.Stability.blockProduct_nonneg hb _ _
  have hmul := mul_le_mul (hQ n s hsn) (hR n s hsn) hRb (le_trans hQa (hQ n s hsn))
  simpa only [BTP.Stability.blockProduct, prod_mul_distrib] using hmul


open BTP.InverseBounds BTP.SemiInfinite

/-- Positivity for the actual signed inverse, with arbitrary nonnegative
factor entries (no Metelmann initial-zero pattern is imposed). -/
theorem actual_inverse_nonneg (a : BTP.Entries) (p : ℕ)
    (ha : ∀ k < p, ∀ t, 0 < t → 0 ≤ a k t) (n s : ℕ) :
    0 ≤ inverseEntries a p n s := by
  let d := max n s+1
  let i : Fin d := ⟨n, by dsimp [d]; omega⟩
  let j : Fin d := ⟨s, by dsimp [d]; omega⟩
  have h := qProduct_nonnegative (d := d) a p (fun k hk t ht _ => ha k hk t ht) i j
  rwa [inverseEntries_finite] at h

/-- The actual signed inverse satisfies the row comparison used above. -/
theorem actual_inverse_row_neighbor (a : BTP.Entries) (p : ℕ) {β : ℝ}
    (hβ : 0 ≤ β) (ha : ∀ k < p+1, ∀ t, 0 < t → β ≤ a k t)
    (n s : ℕ) : β*inverseEntries a (p+1) n s ≤ inverseEntries a (p+1) (n+1) s := by
  rw [inverseEntries_succ]
  have hQ := actual_inverse_nonneg a (p+1)
    (fun k hk t ht => le_trans hβ (ha k hk t ht)) n s
  have htail := actual_inverse_nonneg (fun k t => a (k+1) t) p
    (fun k hk t ht => le_trans hβ (ha (k+1) (by omega) t ht)) (n+1) s
  have hcoef := ha 0 (by omega) (n+1) (by omega)
  nlinarith

theorem mul_bidiagonal_column_general {d : ℕ} (a : ℕ → ℝ)
    (M : BTP.InverseBounds.Square d) (i j k : Fin d) (hk : k.val=j.val+1) :
    (M*BTP.bidiagonal d a) i j = M i j + M i k*a k.val := by
  rw [BTP.bidiagonal, Matrix.mul_add, Matrix.mul_one]
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply]
  congr 1
  rw [sum_eq_single k]
  · rw [ite_eq_left hk]
  · intro l _ hl
    have hne : l.val ≠ j.val+1 := by intro he; apply hl; apply Fin.ext; omega
    rw [ite_eq_right hne, mul_zero]
  · simp

/-- The column comparison is also derived from the genuine inverse
product; it is not an assumed kernel regularity condition. -/
theorem actual_inverse_col_neighbor (a : BTP.Entries) (p : ℕ) {β : ℝ}
    (hβ : 0 ≤ β) (ha : ∀ k < p+1, ∀ t, 0 < t → β ≤ a k t)
    (n s : ℕ) (hs : s < n) :
    β*inverseEntries a (p+1) n (s+1) ≤ inverseEntries a (p+1) n s := by
  let i : Fin (n+1) := ⟨n, by omega⟩
  let j : Fin (n+1) := ⟨s, by omega⟩
  let k : Fin (n+1) := ⟨s+1, by omega⟩
  have he := congrArg (fun M : BTP.InverseBounds.Square (n+1) => M i j)
    (last_column_equation (n+1) a p)
  rw [mul_bidiagonal_column_general (fun t => -a p t) _ i j k (by rfl),
    inverseEntries_finite, inverseEntries_finite, inverseEntries_finite] at he
  change inverseEntries a (p+1) n s + inverseEntries a (p+1) n (s+1)*(-a p (s+1)) =
    inverseEntries a p n s at he
  have hrem := actual_inverse_nonneg a p
    (fun l hl t ht => le_trans hβ (ha l (by omega) t ht)) n s
  have hQ := actual_inverse_nonneg a (p+1)
    (fun l hl t ht => le_trans hβ (ha l hl t ht)) n (s+1)
  have hcoef := ha p (by omega) (s+1) (by omega)
  nlinarith

/-- The complete near-diagonal estimate for the manuscript's actual
signed inverses of positive bidiagonal products. -/
theorem actual_inverse_near_diagonal_bound (a b : BTP.Entries) (p q : ℕ)
    {β Z : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    (ha : ∀ k < p+1, ∀ t, 0 < t → β ≤ a k t)
    (hb : ∀ k < q+1, ∀ t, 0 < t → β ≤ b k t)
    (hZ : ∀ n, ∑ s ∈ range (n+1), inverseEntries a (p+1) n s *
      inverseEntries b (q+1) n s ≤ Z)
    (i j : ℕ) (hij : i ≤ j+max (p+1) (q+1)) (hji : j ≤ i+max (p+1) (q+1)) :
    ∑ uv ∈ ((range (i+1) ×ˢ range (j+1)).filter
      (fun uv => uv.1 ≤ uv.2+(p+1) ∧ uv.2 ≤ uv.1+(q+1))),
      inverseEntries a (p+1) i uv.1 * inverseEntries b (q+1) j uv.2
    ≤ ((p+1)+(q+1)+1 : ℝ)*(β⁻¹)^(2*max (p+1) (q+1))*Z := by
  simpa only [Nat.cast_add, Nat.cast_one] using near_diagonal_sum_bound (inverseEntries a (p+1)) (inverseEntries b (q+1)) hβ hβ1
    (actual_inverse_nonneg a (p+1) (fun k hk t ht => le_trans hβ.le (ha k hk t ht)))
    (actual_inverse_nonneg b (q+1) (fun k hk t ht => le_trans hβ.le (hb k hk t ht)))
    (fun n s _ => actual_inverse_row_neighbor a p hβ.le ha n s)
    (actual_inverse_col_neighbor a p hβ.le ha)
    (fun n s _ => actual_inverse_row_neighbor b q hβ.le hb n s)
    (actual_inverse_col_neighbor b q hβ.le hb) hZ (p+1) (q+1) i j hij hji

end BTP.Stability.BandLDU
