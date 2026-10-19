import RelativeFiniteControl
import RelativeNormalizedControl
import RelativeDiagonalControl

noncomputable section
namespace BTP.RelativeStability
open Finset Matrix BTP BTP.Stability BTP.Stability.BandLDU BTP.GeneralStability
variable {N : ℕ}
local instance : PartialOrder (Mat N) := inferInstanceAs (PartialOrder (Fin N → Fin N → ℝ))

def normalizedData (a b : ℕ → ℕ → ℝ) (p q : ℕ) (d : ℕ → ℝ)
    (ha : ∀ i n,0 < a i n) (hb : ∀ i n,0 < b i n) (hd : ∀ n,0 < d n) : SectionData :=
  actualData (rawReverse (normalizedLast a (p+1)) (p+1))
    (rawReverse (normalizedLast b (q+1)) (q+1)) (p+1) (q+1)
    (scaleDiagonal d (cumulativeWeight (a p)) (cumulativeWeight (b q)))
    (fun n => ne_of_gt (scaleDiagonal_pos d _ _ hd
      (cumulativeWeight_pos (a p) (ha p)) (cumulativeWeight_pos (b q) (hb q)) n))

theorem rawUnitEntry_nonneg {m : ℕ} (l : Fin m → ℕ → ℝ) (hl : ∀ i n,0 < l i n)
    (i j : ℕ) : 0 ≤ rawUnitEntry l i j := by
  unfold rawUnitEntry
  split_ifs
  · exact rawTriangular_nonneg l hl _ _
  · rfl

theorem normalized_finite_control (a b : ℕ → ℕ → ℝ) (p q : ℕ) (d : ℕ → ℝ)
    (ha : ∀ i n,0 < a i n) (hb : ∀ i n,0 < b i n) (hd : ∀ n,0 < d n)
    (hga : ∀ i,i+1 < p+1 → GeometricDecay (fun n => a i n/a (i+1) n))
    (hgb : ∀ i,i+1 < q+1 → GeometricDecay (fun n => b i n/b (i+1) n))
    (hcross : GeometricDecay (crossWeight (a p) (b q) d)) :
    ∃ A B K Z : ℝ,0 ≤ A ∧ 0 ≤ B ∧ 0 ≤ K ∧ 0 ≤ Z ∧
      ∀ N,let s := normalizedData a b p q d ha hb hd
        FiniteRelativeControl (p+1) (q+1) (s.L N) (s.U N) (s.Li N) (s.Ui N)
          (fun i : Fin N => s.d i.val) A B K Z := by
  obtain ⟨Ka,hKa,hca⟩ := sameRow_finite_comparison a ha (p+1) hga
  obtain ⟨Kb,hKb,hcb⟩ := sameRow_finite_comparison b hb (q+1) hgb
  obtain ⟨Ba,hBa,hqa⟩ := normalized_inverse_bound a ha p hga
  obtain ⟨Bb,hBb,hqb⟩ := normalized_inverse_bound b hb q hgb
  obtain ⟨Z,hZ,hrow⟩ := scaled_diagonal_row_bound (a p) (b q) d (ha p) (hb q) hd hcross
  let A₁ : ℝ := 2^(p+1)*Ka^(2*(p+1))
  let A₂ : ℝ := 2^(q+1)*Kb^(2*(q+1))
  have hA₁ : 0 ≤ A₁ := by dsimp [A₁]; positivity
  have hA₂ : 0 ≤ A₂ := by dsimp [A₂]; positivity
  refine ⟨A₁+A₂,Ba+Bb,A₁+A₂,Z,add_nonneg hA₁ hA₂,add_nonneg hBa hBb,
    add_nonneg hA₁ hA₂,hZ,?_⟩
  intro N
  let s := normalizedData a b p q d ha hb hd
  have hl (i j : Fin N) : s.L N i j=
      rawUnitEntry (rawProductBand (normalizedLast a (p+1)) (p+1)) i.val j.val :=
    (congrArg (fun M : Mat N => M i j)
      (rawUnitEntry_productBand_finite (normalizedLast a (p+1)) (p+1) N)).symm
  have hu (i j : Fin N) : s.U N i j=
      rawUnitEntry (rawProductBand (normalizedLast b (q+1)) (q+1)) j.val i.val :=
    (congrArg (fun M : Mat N => M j i)
      (rawUnitEntry_productBand_finite (normalizedLast b (q+1)) (q+1) N)).symm
  have hl0 : 0 ≤ s.L N := by
    intro i j
    rw [hl]
    exact rawUnitEntry_nonneg _ (rawProductBand_pos _ (normalizedLast_pos a ha (p+1)) _) _ _
  have hu0 : 0 ≤ s.U N := by
    intro i j
    rw [hu]
    exact rawUnitEntry_nonneg _ (rawProductBand_pos _ (normalizedLast_pos b hb (q+1)) _) _ _
  refine {
    lowerL := s.lower_L N
    upperU := s.upper_U N
    lowerLi := s.lower_Li N
    upperUi := s.upper_Ui N
    lowerBand := actual_lower_band _ (p+1) N
    upperBand := actual_upper_band _ (q+1) N
    nonnegL := hl0
    nonnegU := hu0
    positiveD := fun i => scaleDiagonal_pos d _ _ hd (cumulativeWeight_pos (a p) (ha p))
      (cumulativeWeight_pos (b q) (hb q)) i.val
    leftInverse := s.L_Li N
    rightInverse := s.Ui_U N
    boundL := ?_
    boundU := ?_
    boundLi := ?_
    boundUi := ?_
    prefixL := ?_
    prefixU := ?_
    rowD := ?_ }
  · intro i j
    rw [hl]
    exact (normalized_product_uniform_bound a ha (p+1) (by omega) hKa hca i.val j.val).trans
      (le_add_of_nonneg_right hA₂)
  · intro i j
    rw [hu]
    exact (normalized_product_uniform_bound b hb (q+1) (by omega) hKb hcb j.val i.val).trans
      (le_add_of_nonneg_left hA₁)
  · intro i j
    exact (hqa N i j).trans (le_add_of_nonneg_right hBb)
  · intro i j
    exact (hqb N j i).trans (le_add_of_nonneg_left hBa)
  · intro i j k hkj hji
    have hh := normalized_product_prefix_bound a ha (p+1) (by omega) hKa hca
      i.val j.val k.val hkj hji
    rw [←hl,←hl] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hA₂) (hl0 i j))
  · intro i j k hki hij
    have hh := normalized_product_prefix_bound b hb (q+1) (by omega) hKb hcb
      j.val i.val k.val hki hij
    rw [←hu,←hu] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hA₁) (hu0 i j))
  · intro j
    change (∑ k ∈ Iic j,scaleDiagonal d (cumulativeWeight (a p)) (cumulativeWeight (b q)) k.val) ≤ _
    rw [fin_sum_Iic_eq_range]
    exact hrow j.val

#print axioms normalized_finite_control
end BTP.RelativeStability
