import ActualPBFData
import FiniteInverseEstimate

/-! The joint-row-sum criterion for the genuine LDU derivative on the
full band. The triangular factors are actual bidiagonal products. -/
noncomputable section
open Matrix Finset
open scoped BigOperators
namespace BTP.Stability.BandLDU
open BTP BTP.SemiInfinite BTP.GeneralStability

theorem actual_invV_bound (a b : Entries) (p q : ℕ) (d : ℕ → ℝ) (hd : ∀ n, d n≠0)
    {β Z : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    (ha : ∀ k  <  p+1, ∀ t, 0 < t → β ≤ a k t)
    (hb : ∀ k  <  q+1, ∀ t, 0 < t → β ≤ b k t)
    (hZ : ∀ n, ∑ s ∈ range (n+1), inverseEntries a (p+1) n s*inverseEntries b (q+1) n s ≤ Z)
    {N : ℕ} (E : FullBand (p+1) (q+1)) (i j : Fin N)
    (hij : i.val ≤ j.val+max (p+1) (q+1)) (hji : j.val ≤ i.val+max (p+1) (q+1)) :
    |(actualData a b (p+1) (q+1) d hd).invV E N i j| ≤ 
      (((p+1)+(q+1)+1 : ℝ)*β⁻¹^(2*max (p+1) (q+1))*Z)*‖E‖ := by
  have h := actual_finite_inverse_sandwich_bound a b p q hβ hβ1 ha hb hZ E
    (actualInverse a (p+1)) (fun i j => actualInverse b (q+1) j i) i j
    (actualInverse_zero a (p+1) i.val) (actualInverse_zero b (q+1) j.val)
    (actualInverse_abs a (p+1) (fun k hk t ht => (hβ.le.trans (ha k hk t ht))) i.val)
    (actualInverse_abs b (q+1) (fun k hk t ht => (hβ.le.trans (hb k hk t ht))) j.val)
    hij hji
  have hl : restrictedMatrix (actualInverse a (p+1)) N = (lowerProduct N a (p+1))⁻¹ := by
    ext i j; exact actualInverse_finite a (p+1) N i j
  have hu : restrictedMatrix (fun i j => actualInverse b (q+1) j i) N =
      ((lowerProduct N b (q+1))⁻¹).transpose := by
    ext i j; exact actualInverse_finite b (q+1) N j i
  rw [hl,hu] at h
  exact h

theorem actual_uniform_inverse_bounds (a b : Entries) (p q : ℕ) (d : ℕ → ℝ)
    (hd : ∀ n, d n≠0) {β A D Z : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hA : 0 ≤ A) (hD : 0 ≤ D)
    (ha : ∀ k  <  p+1, ∀ t, 0 < t → β ≤ a k t)
    (hb : ∀ k  <  q+1, ∀ t, 0 < t → β ≤ b k t)
    (haA : ∀ k  <  p+1, ∀ t, 0 < t → |a k t| ≤ A)
    (hbA : ∀ k  <  q+1, ∀ t, 0 < t → |b k t| ≤ A)
    (hdD : ∀ n, |(d n)⁻¹| ≤ D)
    (hZ : ∀ n, ∑ s ∈ range (n+1), inverseEntries a (p+1) n s*inverseEntries b (q+1) n s ≤ Z) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ (E : FullBand (p+1) (q+1)) N i j,
        |(actualData a b (p+1) (q+1) d hd).invX E N i j| ≤ C*‖E‖) ∧
      (∀ (E : FullBand (p+1) (q+1)) N i j,
        |(actualData a b (p+1) (q+1) d hd).invZ E N i j| ≤ C*‖E‖) ∧
      (∀ (E : FullBand (p+1) (q+1)) N i j,
        |(actualData a b (p+1) (q+1) d hd).invY E N i j| ≤ C*‖E‖) := by
  let S := actualData a b (p+1) (q+1) d hd
  let K := (((p+1)+(q+1)+1 : ℝ)*β⁻¹^(2*max (p+1) (q+1))*Z)
  let M₁ := (1+A)^(p+1)
  let M₂ := (1+A)^(q+1)
  let C₁ := (p+2 : ℝ)*M₁*D*K
  let C₂ := (q+2 : ℝ)*M₂*D*K
  have hZ0 : 0 ≤ Z := by
    have h := hZ 0
    simp only [Nat.zero_add, sum_range_one, inverseEntries_zero_row, ite_true, mul_one] at h
    linarith
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hM₁ : 0 ≤ M₁ := by dsimp [M₁]; positivity
  have hM₂ : 0 ≤ M₂ := by dsimp [M₂]; positivity
  have hC₁ : 0 ≤ C₁ := by dsimp [C₁]; positivity
  have hC₂ : 0 ≤ C₂ := by dsimp [C₂]; positivity
  have hV (E : FullBand (p+1) (q+1)) (N : ℕ) (i j : Fin N)
      (hij : i.val ≤ j.val+max (p+1) (q+1)) (hji : j.val ≤ i.val+max (p+1) (q+1)) :
      |S.invV E N i j| ≤ K*‖E‖ := actual_invV_bound a b p q d hd hβ hβ1 ha hb hZ E i j hij hji
  refine ⟨C₁+K+C₂, by positivity, ?_, ?_, ?_⟩
  · intro E N i j
    have hbnd := (S.inv_bands (actual_lower_band a (p+1)) (actual_upper_band b (q+1)) E N).1
    have ht := (S.inv_triangular E N).1
    have hc : |S.invX E N i j| ≤ C₁*‖E‖ := by
      by_cases hji : j ≤ i
      · by_cases hij : i.val ≤ j.val+(p+1)
        · have he := lower_variation_near_bound (p:=p+1) (S.L N) (S.invV E N)
            (fun i => (d i.val)⁻¹) hM₁ hD (mul_nonneg hK (norm_nonneg E))
            (S.lower_L N) (actual_lower_uniform_bound a hA (p+1) haA N)
            (fun i => hdD i.val)
            (fun i j hj hi => hV E N i j (by omega) (by omega)) i j hji hij
          calc
            _ ≤ ((p+1 : ℕ)+1 : ℝ)*M₁*D*(K*‖E‖) := he
            _ = C₁*‖E‖ := by dsimp [C₁]; push_cast; ring
        · rw [hbnd i j (by omega)]
          simpa only [abs_zero] using mul_nonneg hC₁ (norm_nonneg E)
      · rw [ht i j (le_of_not_ge hji)]
        simpa only [abs_zero] using mul_nonneg hC₁ (norm_nonneg E)
    exact hc.trans (mul_le_mul_of_nonneg_right (by linarith : C₁ ≤ C₁+K+C₂) (norm_nonneg E))
  · intro E N i j
    have hc : |S.invZ E N i j| ≤ K*‖E‖ := by
      by_cases hij : i=j
      · subst j
        simpa only [SectionData.invZ, diagPart, Matrix.diagonal_apply_eq] using
          hV E N i i (by omega) (by omega)
      · rw [(S.inv_triangular E N).2.1 i j hij]
        simpa only [abs_zero] using mul_nonneg hK (norm_nonneg E)
    exact hc.trans (mul_le_mul_of_nonneg_right (by linarith : K ≤ C₁+K+C₂) (norm_nonneg E))
  · intro E N i j
    have hbnd := (S.inv_bands (actual_lower_band a (p+1)) (actual_upper_band b (q+1)) E N).2
    have ht := (S.inv_triangular E N).2.2
    have hc : |S.invY E N i j| ≤ C₂*‖E‖ := by
      by_cases hij : i ≤ j
      · by_cases hji : j.val ≤ i.val+(q+1)
        · have he := upper_variation_near_bound (q:=q+1) (S.U N) (S.invV E N)
            (fun i => (d i.val)⁻¹) hM₂ hD (mul_nonneg hK (norm_nonneg E))
            (S.upper_U N) (fun i j => actual_lower_uniform_bound b hA (q+1) hbA N j i)
            (fun i => hdD i.val)
            (fun i j hi hj => hV E N i j (by omega) (by omega)) i j hij hji
          calc
            _ ≤ ((q+1 : ℕ)+1 : ℝ)*M₂*D*(K*‖E‖) := he
            _ = C₂*‖E‖ := by dsimp [C₂]; push_cast; ring
        · rw [hbnd i j (by omega)]
          simpa only [abs_zero] using mul_nonneg hC₂ (norm_nonneg E)
      · rw [ht i j (le_of_not_ge hij)]
        simpa only [abs_zero] using mul_nonneg hC₂ (norm_nonneg E)
    exact hc.trans (mul_le_mul_of_nonneg_right (by linarith : C₂ ≤ C₁+K+C₂) (norm_nonneg E))

/-- Necessary and sufficient joint-row-sum criterion for the actual
normalized LDU derivative, for arbitrary positive lower/upper bandwidths.
The identity `IsDerivative` specifies the operator by finite matrix
multiplication. Invertibility is proved, never assumed. -/
theorem ldu_derivative_row_criterion (a b : Entries) (p q : ℕ) (d : ℕ → ℝ)
    (hd : ∀ n, d n≠0) {β M D : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hM : 0 ≤ M) (hD : 0 ≤ D)
    (ha : ∀ k < p+1, ∀ t, 0 < t → β ≤ a k t)
    (hb : ∀ k < q+1, ∀ t, 0 < t → β ≤ b k t)
    (haM : ∀ k < p+1, ∀ t, 0 < t → |a k t| ≤ M)
    (hbM : ∀ k < q+1, ∀ t, 0 < t → |b k t| ≤ M)
    (hdD : ∀ n, |(d n)⁻¹| ≤ D)
    (A : FullBand (p+1) (q+1) →L[ℝ] FullBand (p+1) (q+1))
    (hA : (actualData a b (p+1) (q+1) d hd).IsDerivative A) :
    (∃ J : FullBand (p+1) (q+1) ≃L[ℝ] FullBand (p+1) (q+1), ∀ E, J E=A E) ↔
      ∃ Z : ℝ, ∀ n, ∑ s ∈ range (n+1),
        inverseEntries a (p+1) n s*inverseEntries b (q+1) n s ≤ Z := by
  constructor
  · rintro ⟨J,hJ⟩
    let F := J.symm (identityBand (p+1) (q+1))
    refine ⟨‖F‖, actual_row_bound_of_identity_solution a b (p+1) (q+1) d hd A hA F ?_⟩
    rw [← hJ F]
    exact J.apply_symm_apply _
  · rintro ⟨Z,hZ⟩
    obtain ⟨C,_,hX,hV,hY⟩ := actual_uniform_inverse_bounds a b p q d hd hβ hβ1
      hM hD ha hb haM hbM hdD hZ
    let S := actualData a b (p+1) (q+1) d hd
    refine ⟨S.derivativeEquiv (actual_lower_band a (p+1))
      (actual_upper_band b (q+1)) C hX hV hY A hA, ?_⟩
    intro E
    rfl

#print axioms ldu_derivative_row_criterion
end BTP.Stability.BandLDU
