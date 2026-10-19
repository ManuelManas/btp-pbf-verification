import InverseDominance
import ActualPBFData

/-! The genuine weighted signed-inverse row sums in relative LDU.
All three original families may be unbounded. -/
noncomputable section
open Finset
namespace BTP.RelativeStability
open BTP BTP.Stability BTP.Stability.BandLDU BTP.SemiInfinite BTP.GeneralStability

def crossWeight (a b d : ℕ → ℝ) (n : ℕ) : ℝ := a n*b n*d (n-1)/d n

theorem cross_product (a b d : ℕ → ℝ) (hd : ∀ n,d n≠0) (s N : ℕ) :
    blockProduct (crossWeight a b d) s N =
      blockProduct a s N*blockProduct b s N*d s/d (s+N) := by
  induction N with
  | zero => simp [hd]
  | succ N ih =>
    rw [blockProduct_succ,blockProduct_succ,blockProduct_succ,ih]
    simp only [crossWeight,show s+N+1-1=s+N by omega,
      show s+(N+1)=s+N+1 by omega]
    field_simp [hd]

def relativeJointRow (a b : Entries) (p q : ℕ) (d : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ s ∈ range (n+1), inverseEntries a p n s*inverseEntries b q n s*d s/d n

theorem relative_joint_rows_bounded (a b : Entries) (p q : ℕ) (d : ℕ → ℝ)
    (ha : ∀ i≤p,∀ n,0<a i n) (hb : ∀ j≤q,∀ n,0<b j n) (hd : ∀ n,0<d n)
    (hga : ∀ i<p,GeometricDecay (fun n => a (i+1) n/a i n))
    (hgb : ∀ j<q,GeometricDecay (fun n => b (j+1) n/b j n))
    (hcross : GeometricDecay (crossWeight (a 0) (b 0) d)) :
    ∃ Z : ℝ,∀ n,relativeJointRow a b (p+1) (q+1) d n≤Z := by
  obtain ⟨C,hC,hqa⟩ := actual_inverse_last_factor_dominance a p ha hga
  obtain ⟨D,hD,hqb⟩ := actual_inverse_last_factor_dominance b q hb hgb
  have hc : ∀ n,0≤crossWeight (a 0) (b 0) d n := by
    intro n
    exact div_nonneg (mul_nonneg (mul_nonneg (ha 0 (by omega) n).le (hb 0 (by omega) n).le) (hd _).le) (hd n).le
  obtain ⟨M,hM⟩ := (rowSum_bounded_iff_geometric hc).mpr hcross
  refine ⟨C*D*M,?_⟩
  intro n
  calc
    _ ≤ ∑ s ∈ range (n+1),
        (C*blockProduct (a 0) s (n-s))*(D*blockProduct (b 0) s (n-s))*d s/d n := by
      apply sum_le_sum
      intro s hs
      have hsn : s≤n := by simpa using hs
      apply div_le_div_of_nonneg_right _ (hd n).le
      apply mul_le_mul_of_nonneg_right _ (hd s).le
      apply mul_le_mul (hqa n s hsn) (hqb n s hsn)
      · exact actual_inverse_nonneg b (q+1) (fun j hj t _ => (hb j (by omega) t).le) n s
      · exact mul_nonneg hC (blockProduct_pos (a 0) (ha 0 (by omega)) s (n-s)).le
    _ = C*D*rowSum (crossWeight (a 0) (b 0) d) n := by
      rw [rowSum_eq_sum,mul_sum]
      apply sum_congr rfl
      intro s hs
      have hsn : s≤n := by simpa using hs
      rw [cross_product _ _ _ (fun n => ne_of_gt (hd n)),Nat.add_sub_of_le hsn]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hM n) (mul_nonneg hC hD)

theorem relative_joint_rows_imply_cross (a b : Entries) (p q : ℕ) (d : ℕ → ℝ)
    (ha : ∀ i≤p,∀ n,0<a i n) (hb : ∀ j≤q,∀ n,0<b j n) (hd : ∀ n,0<d n)
    (hrows : ∃ Z : ℝ,∀ n,relativeJointRow a b (p+1) (q+1) d n≤Z) :
    GeometricDecay (crossWeight (a 0) (b 0) d) := by
  have hc : ∀ n,0≤crossWeight (a 0) (b 0) d n := by
    intro n
    exact div_nonneg (mul_nonneg (mul_nonneg (ha 0 (by omega) n).le (hb 0 (by omega) n).le) (hd _).le) (hd n).le
  apply (rowSum_bounded_iff_geometric hc).mp
  obtain ⟨Z,hZ⟩ := hrows
  refine ⟨Z,?_⟩
  intro n
  apply le_trans _ (hZ n)
  rw [rowSum_eq_sum]
  apply sum_le_sum
  intro s hs
  have hsn : s≤n := by simpa using hs
  rw [cross_product _ _ _ (fun n => ne_of_gt (hd n)),Nat.add_sub_of_le hsn]
  have hqa := actual_inverse_last_lower a p (fun i hi t _ => (ha i (by omega) t).le) s (n-s)
  have hqb := actual_inverse_last_lower b q (fun i hi t _ => (hb i (by omega) t).le) s (n-s)
  rw [Nat.add_sub_of_le hsn] at hqa hqb
  apply div_le_div_of_nonneg_right _ (hd n).le
  apply mul_le_mul_of_nonneg_right _ (hd s).le
  exact mul_le_mul hqa hqb
    (blockProduct_pos (b 0) (hb 0 (by omega)) s (n-s)).le
    (actual_inverse_nonneg a (p+1) (fun i hi t _ => (ha i (by omega) t).le) n s)

theorem relative_joint_row_criterion (a b : Entries) (p q : ℕ) (d : ℕ → ℝ)
    (ha : ∀ i≤p,∀ n,0<a i n) (hb : ∀ j≤q,∀ n,0<b j n) (hd : ∀ n,0<d n)
    (hga : ∀ i<p,GeometricDecay (fun n => a (i+1) n/a i n))
    (hgb : ∀ j<q,GeometricDecay (fun n => b (j+1) n/b j n)) :
    (∃ Z : ℝ,∀ n,relativeJointRow a b (p+1) (q+1) d n≤Z) ↔
      GeometricDecay (crossWeight (a 0) (b 0) d) :=
  ⟨relative_joint_rows_imply_cross a b p q d ha hb hd,
    relative_joint_rows_bounded a b p q d ha hb hd hga hgb⟩

#print axioms relative_joint_row_criterion

end BTP.RelativeStability
