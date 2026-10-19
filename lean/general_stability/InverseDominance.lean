import FullBandStability
import LowerGeneralCriterion

/-! Uniform domination of a signed inverse by its last original
bidiagonal factor. Legacy factor indices run from right to left. -/

noncomputable section
open Finset
namespace BTP.Stability.BandLDU
open BTP BTP.SemiInfinite BTP.GeneralStability

theorem blockProduct_pos (w : ℕ → ℝ) (hw : ∀ n, 0<w n) (s N : ℕ) :
    0<blockProduct w s N :=
  prod_pos (fun _ _ => hw _)

theorem blockProduct_div (a b : ℕ → ℝ) (s N : ℕ) :
    blockProduct (fun n => a n/b n) s N =
      blockProduct a s N / blockProduct b s N := by
  simp only [blockProduct, prod_div_distrib]

theorem inverseEntries_normalized_step (a : Entries) (p s N : ℕ)
    (ha : ∀ n, 0<a 0 n) :
    inverseEntries a (p+1) (s+N+1) s / blockProduct (a 0) s (N+1) =
      inverseEntries (fun i n => a (i+1) n) p (s+N+1) s /
        blockProduct (a 0) s (N+1) +
      inverseEntries a (p+1) (s+N) s / blockProduct (a 0) s N := by
  rw [inverseEntries_succ, blockProduct_succ]
  have h0 := ne_of_gt (blockProduct_pos (a 0) ha s N)
  have h1 := ne_of_gt (ha (s+N+1))
  field_simp

theorem inverseEntries_normalized_sum (a : Entries) (p s N : ℕ)
    (ha : ∀ n, 0<a 0 n) :
    inverseEntries a (p+1) (s+N) s / blockProduct (a 0) s N =
      1 + ∑ t ∈ range N,
        inverseEntries (fun i n => a (i+1) n) p (s+t+1) s /
          blockProduct (a 0) s (t+1) := by
  induction N with
  | zero => simp [inverseEntries_diagonal]
  | succ N ih =>
    rw [show s+(N+1)=s+N+1 by omega, inverseEntries_normalized_step a p s N ha,
      ih, sum_range_succ]
    ring

theorem inverse_dominance_step (a : Entries) (p : ℕ)
    (ha : ∀ n, 0<a 0 n) {C : ℝ} (hC : 0≤C)
    (htail : ∀ n s, s≤n →
      inverseEntries (fun i t => a (i+1) t) p n s ≤ C*blockProduct (a 1) s (n-s))
    (hg : GeometricDecay (fun n => a 1 n/a 0 n)) :
    ∃ D : ℝ, 0≤D ∧ ∀ n s, s≤n → inverseEntries a (p+1) n s ≤ D*blockProduct (a 0) s (n-s) := by
  rcases hg with ⟨K,ρ,hK,hρ,hρ1,hgeo⟩
  refine ⟨1+C*K/(1-ρ),by positivity,?_⟩
  intro n s hsn
  have hp := blockProduct_pos (a 0) ha s (n-s)
  apply (div_le_iff₀ hp).mp
  have hsum := inverseEntries_normalized_sum a p s (n-s) ha
  rw [Nat.add_sub_of_le hsn] at hsum
  rw [hsum]
  have ht (t : ℕ) :
      inverseEntries (fun i n => a (i+1) n) p (s+t+1) s /
        blockProduct (a 0) s (t+1) ≤ C*K*ρ^(t+1) := by
    calc
      _ ≤ (C*blockProduct (a 1) s (t+1))/blockProduct (a 0) s (t+1) := by
        apply div_le_div_of_nonneg_right _ (blockProduct_pos (a 0) ha s (t+1)).le
        have hh := htail (s+t+1) s (by omega)
        rw [show s+t+1-s=t+1 by omega] at hh
        exact hh
      _ = C*blockProduct (fun n => a 1 n/a 0 n) s (t+1) := by
        rw [blockProduct_div]; ring
      _ ≤ C*(K*ρ^(t+1)) := mul_le_mul_of_nonneg_left (hgeo s (t+1)) hC
      _ = _ := by ring
  have hsumBound : (∑ t ∈ range (n-s), ρ^(t+1))≤1/(1-ρ) := by
    calc
      _ ≤ ∑ t ∈ range (n-s), ρ^t := by
        apply sum_le_sum
        intro t _
        rw [pow_succ]
        exact mul_le_of_le_one_right (pow_nonneg hρ.le t) hρ1.le
      _ ≤ _ := geometric_partial_sum_le hρ.le hρ1 (n-s)
  calc
    _ ≤ 1 + ∑ t ∈ range (n-s), C*K*ρ^(t+1) := add_le_add le_rfl (sum_le_sum (fun t _ => ht t))
    _ = 1+C*K*(∑ t ∈ range (n-s), ρ^(t+1)) := by rw [mul_sum]
    _ ≤ 1+C*K*(1/(1-ρ)) := add_le_add le_rfl
      (mul_le_mul_of_nonneg_left hsumBound (mul_nonneg hC (le_trans zero_le_one hK)))
    _ = _ := by ring

theorem inverseEntries_one (a : Entries) (s N : ℕ) :
    inverseEntries a 1 (s+N) s = blockProduct (a 0) s N := by
  induction N with
  | zero => simp [inverseEntries_diagonal]
  | succ N ih =>
    rw [show s+(N+1)=s+N+1 by omega, inverseEntries_succ, ih, blockProduct_succ]
    have hz : inverseEntries (fun i n => a (i+1) n) 0 (s+N+1) s=0 := by
      simp [inverseEntries, show s+N+1≠s by omega]
    rw [hz]
    ring

theorem actual_inverse_last_factor_dominance (a : Entries) (p : ℕ)
    (ha : ∀ i≤p, ∀ n, 0<a i n)
    (hg : ∀ i<p, GeometricDecay (fun n => a (i+1) n/a i n)) :
    ∃ C : ℝ, 0≤C ∧ ∀ n s, s≤n →
      inverseEntries a (p+1) n s≤C*blockProduct (a 0) s (n-s) := by
  induction p generalizing a with
  | zero =>
    refine ⟨1,zero_le_one,?_⟩
    intro n s hsn
    have hh := inverseEntries_one a s (n-s)
    rw [Nat.add_sub_of_le hsn] at hh
    simp [hh]
  | succ p ih =>
    obtain ⟨C,hC,htail⟩ := ih (fun i n => a (i+1) n)
      (fun i hi n => ha (i+1) (by omega) n)
      (fun i hi => hg (i+1) (by omega))
    exact inverse_dominance_step a (p+1) (ha 0 (by omega)) hC htail (hg 0 (by omega))

#print axioms actual_inverse_last_factor_dominance

theorem actual_joint_rows_bounded_of_geometric (a b : Entries) (p q : ℕ)
    (ha : ∀ i≤p, ∀ n, 0<a i n) (hb : ∀ j≤q, ∀ n, 0<b j n)
    (hga : ∀ i<p, GeometricDecay (fun n => a (i+1) n/a i n))
    (hgb : ∀ j<q, GeometricDecay (fun n => b (j+1) n/b j n))
    (hcross : GeometricDecay (fun n => a 0 n*b 0 n)) :
    ∃ Z : ℝ, ∀ n, ∑ s ∈ range (n+1),
      inverseEntries a (p+1) n s*inverseEntries b (q+1) n s≤Z := by
  obtain ⟨C,hC,hqa⟩ := actual_inverse_last_factor_dominance a p ha hga
  obtain ⟨D,hD,hqb⟩ := actual_inverse_last_factor_dominance b q hb hgb
  obtain ⟨M,hM⟩ := (rowSum_bounded_iff_geometric
    (fun n => mul_nonneg (ha 0 (by omega) n).le (hb 0 (by omega) n).le)).mpr hcross
  refine ⟨C*D*M,?_⟩
  intro n
  calc
    _ ≤ ∑ s ∈ range (n+1),
        (C*blockProduct (a 0) s (n-s))*(D*blockProduct (b 0) s (n-s)) := by
      apply sum_le_sum
      intro s hs
      have hsn : s≤n := by simpa using hs
      apply mul_le_mul (hqa n s hsn) (hqb n s hsn)
      · exact actual_inverse_nonneg b (q+1) (fun j hj t _ => (hb j (by omega) t).le) n s
      · exact mul_nonneg hC (blockProduct_pos (a 0) (ha 0 (by omega)) s (n-s)).le
    _ = C*D*rowSum (fun n => a 0 n*b 0 n) n := by
      rw [rowSum_eq_sum,mul_sum]
      apply sum_congr rfl
      intro s _
      simp only [blockProduct,prod_mul_distrib]
      ring
    _ ≤ C*D*M := mul_le_mul_of_nonneg_left (hM n) (mul_nonneg hC hD)

#print axioms actual_joint_rows_bounded_of_geometric

theorem shifted_ratio_product (u v : ℕ → ℝ) (hv : ∀ n, v n≠0) (s N : ℕ) :
    blockProduct (fun n => u n/v n) (s+1) N =
      blockProduct (fun n => u (n+1)/v n) s N * v (s+1)/v (s+N+1) := by
  induction N with
  | zero => simp [hv]
  | succ N ih =>
    rw [blockProduct_succ,blockProduct_succ,ih]
    simp only [show s+1+N+1=s+N+1+1 by omega,
      show s+(N+1)+1=s+N+1+1 by omega]
    field_simp

theorem geometric_same_row_of_shifted (u v : ℕ → ℝ)
    {α A : ℝ} (hα : 0<α) (hu : ∀ n,0<u n)
    (hv : ∀ n, α≤v n) (hA : ∀ n, v n≤A)
    (hg : GeometricDecay (fun n => u (n+1)/v n)) :
    GeometricDecay (fun n => u n/v n) := by
  have hvp : ∀ n,0<v n := fun n => lt_of_lt_of_le hα (hv n)
  have hAp : 0<A := lt_of_lt_of_le (hvp 0) (hA 0)
  apply (GeometricDecay.shift_iff (fun n => div_nonneg (hu n).le (hvp n).le) 1).mp
  rcases hg with ⟨C,ρ,hC,hρ,hρ1,hprod⟩
  refine ⟨1+C*(A/α),ρ,?_,hρ,hρ1,?_⟩
  · have : 0≤C*(A/α) := mul_nonneg (le_trans zero_le_one hC) (div_nonneg hAp.le hα.le)
    linarith
  intro s N
  rw [BTP.FreeScalar.blockProduct_shift (fun n => u n/v n) 1 s N,show 1+s=s+1 by omega,
    shifted_ratio_product u v (fun n => ne_of_gt (hvp n))]
  have hratio : v (s+1)/v (s+N+1)≤A/α := by
    apply (div_le_iff₀ (hvp _)).mpr
    have hh := mul_le_mul_of_nonneg_left (hv (s+N+1)) (div_nonneg hAp.le hα.le)
    have he : A/α*α=A := by field_simp
    rw [he] at hh
    exact (hA _).trans hh
  have hmul := mul_le_mul (hprod s N) hratio
    (div_nonneg (hvp _).le (hvp _).le)
    (mul_nonneg (le_trans zero_le_one hC) (pow_nonneg hρ.le N))
  have hpow : 0≤ρ^N := pow_nonneg hρ.le N
  calc
    _ = blockProduct (fun n => u (n+1)/v n) s N * (v (s+1)/v (s+N+1)) := by ring
    _ ≤ (C*ρ^N)*(A/α) := hmul
    _ ≤ (1+C*(A/α))*ρ^N := by nlinarith only [hpow]

#print axioms geometric_same_row_of_shifted

end BTP.Stability.BandLDU
