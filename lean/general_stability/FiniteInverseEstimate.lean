import FullBandStability
import BandSpaces

noncomputable section
open Finset
open scoped BigOperators
namespace BTP.Stability.BandLDU
open BTP.GeneralStability

def restrictedMatrix (f : ℕ → ℕ → ℝ) (N : ℕ) : Mat N := fun i j => f i.val j.val


theorem sum_range_truncate (f : ℕ → ℝ) {k N : ℕ} (hk : k ≤ N)
    (hz : ∀ n, k ≤ n → n < N → f n=0) :
    ∑ n ∈ range N, f n = ∑ n ∈ range k, f n := by
  symm
  apply sum_subset (range_mono hk)
  intro n hn hnk
  exact hz n (by simpa using hnk) (mem_range.mp hn)

/-- The double sum for a finite triangular sandwich uses only indices
up to its row and column. No inverse-operator boundedness is assumed. -/
theorem triangular_sandwich_sum (li ui e : ℕ → ℕ → ℝ) (N : ℕ) (i j : Fin N)
    (hli : ∀ s, i.val < s → li i.val s=0)
    (hui : ∀ s, j.val < s → ui s j.val=0) :
    ((restrictedMatrix li N) * (restrictedMatrix e N) *
      (restrictedMatrix ui N)) i j =
    ∑ uv ∈ range (i.val+1) ×ˢ range (j.val+1),
      li i.val uv.1 * e uv.1 uv.2 * ui uv.2 j.val := by
  rw [Matrix.mul_assoc]
  simp only [Matrix.mul_apply, restrictedMatrix, mul_sum]
  have hinner (s : Fin N) :
      (∑ v : Fin N, li i.val s.val * (e s.val v.val * ui v.val j.val)) =
      ∑ v ∈ range N, li i.val s.val * (e s.val v * ui v j.val) :=
    Fin.sum_univ_eq_sum_range (fun v => li i.val s.val * (e s.val v * ui v j.val)) N
  simp_rw [hinner]
  rw [Fin.sum_univ_eq_sum_range (fun s => ∑ v ∈ range N, li i.val s * (e s v * ui v j.val)) N]
  rw [sum_product]
  have ht (s : ℕ) :
      ∑ v ∈ range N, li i.val s * (e s v * ui v j.val) =
      ∑ v ∈ range (j.val+1), li i.val s * (e s v * ui v j.val) := by
    apply sum_range_truncate _ (by omega)
    intro v hv _
    rw [hui v (by omega), mul_zero, mul_zero]
  simp_rw [ht]
  rw [sum_range_truncate (fun s => ∑ v ∈ range (j.val+1), li i.val s*(e s v*ui v j.val))
    (show i.val+1 ≤ N by omega) (by
      intro s hs _; simp [hli s (by omega)])]
  apply sum_congr rfl
  intro s _
  apply sum_congr rfl
  intro v _
  ring

theorem triangular_band_sandwich_sum {p q N : ℕ} (E : FullBand p q)
    (li ui : ℕ → ℕ → ℝ) (i j : Fin N)
    (hli : ∀ s, i.val < s → li i.val s=0)
    (hui : ∀ s, j.val < s → ui s j.val=0) :
    ((restrictedMatrix li N) * fullSection E N *
      (restrictedMatrix ui N)) i j =
    ∑ uv ∈ ((range (i.val+1) ×ˢ range (j.val+1)).filter
        (fun uv => uv.1 ≤ uv.2+p ∧ uv.2 ≤ uv.1+q)),
      li i.val uv.1 * fullEntry E uv.1 uv.2 * ui uv.2 j.val := by
  rw [show fullSection E N = restrictedMatrix (fullEntry E) N by rfl,
    triangular_sandwich_sum li ui (fullEntry E) N i j hli hui]
  symm
  apply sum_subset (filter_subset _ _)
  intro uv huv hnot
  have hn : ¬(uv.1 ≤ uv.2+p ∧ uv.2 ≤ uv.1+q) := by simpa [huv] using hnot
  have hb : uv.2+p < uv.1 ∨ uv.1+q < uv.2 := by omega
  rw [fullEntry_band E _ _ hb, mul_zero, zero_mul]

/-- Passing from the actual finite inverse product to the positive
kernel estimate loses only the coefficient norm of E. -/
theorem triangular_band_sandwich_abs {p q N : ℕ} (E : FullBand p q)
    (li ui Q R : ℕ → ℕ → ℝ) (i j : Fin N)
    (hli : ∀ s, i.val < s → li i.val s=0)
    (hui : ∀ s, j.val < s → ui s j.val=0)
    (hQ : ∀ s, |li i.val s|=Q i.val s) (hR : ∀ s, |ui s j.val|=R j.val s) :
    |((restrictedMatrix li N) * fullSection E N *
      (restrictedMatrix ui N)) i j| ≤
    ‖E‖ * ∑ uv ∈ ((range (i.val+1) ×ˢ range (j.val+1)).filter
        (fun uv => uv.1 ≤ uv.2+p ∧ uv.2 ≤ uv.1+q)), Q i.val uv.1*R j.val uv.2 := by
  rw [triangular_band_sandwich_sum E li ui i j hli hui, mul_sum]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro uv _
  rw [abs_mul, abs_mul]
  have h := mul_le_mul_of_nonneg_left (fullEntry_abs_le E uv.1 uv.2) (abs_nonneg (li i.val uv.1))
  have h' := mul_le_mul_of_nonneg_right h (abs_nonneg (ui uv.2 j.val))
  rw [hQ, hR] at h' ⊢
  nlinarith only [h']

/-- Uniform bound for a genuine finite-section inverse sandwich, for
arbitrary bandwidths. The constant is independent of section size N. -/
theorem actual_finite_inverse_sandwich_bound (a b : BTP.Entries) (p q : ℕ)
    {β Z : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    (ha : ∀ k < p+1, ∀ t, 0 < t → β ≤ a k t)
    (hb : ∀ k < q+1, ∀ t, 0 < t → β ≤ b k t)
    (hZ : ∀ n, ∑ s ∈ range (n+1), BTP.SemiInfinite.inverseEntries a (p+1) n s *
      BTP.SemiInfinite.inverseEntries b (q+1) n s ≤ Z)
    {N : ℕ} (E : FullBand (p+1) (q+1)) (li ui : ℕ → ℕ → ℝ) (i j : Fin N)
    (hli : ∀ s, i.val < s → li i.val s=0)
    (hui : ∀ s, j.val < s → ui s j.val=0)
    (hQ : ∀ s, |li i.val s|=BTP.SemiInfinite.inverseEntries a (p+1) i.val s)
    (hR : ∀ s, |ui s j.val|=BTP.SemiInfinite.inverseEntries b (q+1) j.val s)
    (hij : i.val ≤ j.val+max (p+1) (q+1))
    (hji : j.val ≤ i.val+max (p+1) (q+1)) :
    |((restrictedMatrix li N) * fullSection E N *
      (restrictedMatrix ui N)) i j| ≤
    (((p+1)+(q+1)+1 : ℝ)*(β⁻¹)^(2*max (p+1) (q+1))*Z)*‖E‖ := by
  apply (triangular_band_sandwich_abs E li ui _ _ i j hli hui hQ hR).trans
  have h := mul_le_mul_of_nonneg_left
    (actual_inverse_near_diagonal_bound a b p q hβ hβ1 ha hb hZ i.val j.val hij hji) (norm_nonneg E)
  simpa only [mul_comm] using h

theorem lower_variation_near_bound {N p : ℕ} (L V : Mat N) (dinv : Fin N → ℝ)
    {M D K : ℝ} (hM : 0 ≤ M) (_hD : 0 ≤ D) (hK : 0 ≤ K)
    (hL : Lower L) (hLM : ∀ i j, |L i j| ≤ M) (hd : ∀ j, |dinv j| ≤ D)
    (hV : ∀ i j : Fin N, j ≤ i → i.val ≤ j.val+p → |V i j| ≤ K)
    (i j : Fin N) (hji : j ≤ i) (hij : i.val ≤ j.val+p) :
    |(L*lowerPart V*Matrix.diagonal dinv) i j| ≤ (p+1 : ℝ)*M*D*K := by
  rw [Matrix.mul_diagonal,abs_mul]
  have hs : (L*lowerPart V) i j = ∑ k ∈ Icc j i, L i k*lowerPart V k j := by
    rw [Matrix.mul_apply]
    symm
    apply sum_subset (subset_univ _)
    intro k _ hk
    have hn : ¬(j ≤ k ∧ k ≤ i) := by simpa using hk
    by_cases hki : i < k
    · rw [hL i k hki,zero_mul]
    · have hkj : k ≤ j := by exact le_of_lt (lt_of_not_ge (fun hjk => hn ⟨hjk,le_of_not_gt hki⟩))
      simp [lowerPart,not_lt.mpr hkj]
  have hv (k : Fin N) (hk : k ∈ Icc j i) : |lowerPart V k j| ≤ K := by
    have hh := mem_Icc.mp hk
    unfold lowerPart
    split_ifs with ht
    · exact hV k j hh.1 (by exact le_trans hh.2 hij)
    · simpa using hK
  have hb : |(L*lowerPart V) i j| ≤ (p+1 : ℝ)*M*K := by
    rw [hs]
    apply (abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ k ∈ Icc j i, M*K := by
        apply sum_le_sum
        intro k hk
        rw [abs_mul]
        exact mul_le_mul (hLM i k) (hv k hk) (abs_nonneg _) hM
      _ = ((Icc j i).card : ℝ)*(M*K) := by simp
      _ ≤ (p+1 : ℝ)*M*K := by
        have hc : ((Icc j i).card : ℝ) ≤ (p+1 : ℝ) := by
          exact_mod_cast (show (Icc j i).card ≤ p+1 by rw [Fin.card_Icc]; omega)
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hc (mul_nonneg hM hK)
  have hh := mul_le_mul hb (hd j) (abs_nonneg _) (by positivity)
  nlinarith only [hh]

theorem upper_variation_near_bound {N q : ℕ} (U V : Mat N) (dinv : Fin N → ℝ)
    {M D K : ℝ} (hM : 0 ≤ M) (hD : 0 ≤ D) (hK : 0 ≤ K)
    (hU : Upper U) (hUM : ∀ i j, |U i j| ≤ M) (hd : ∀ j, |dinv j| ≤ D)
    (hV : ∀ i j : Fin N, i ≤ j → j.val ≤ i.val+q → |V i j| ≤ K)
    (i j : Fin N) (hij : i ≤ j) (hji : j.val ≤ i.val+q) :
    |(Matrix.diagonal dinv*upperPart V*U) i j| ≤ (q+1 : ℝ)*M*D*K := by
  have hUt : Lower U.transpose := by intro i j hij; exact hU j i hij
  have hVt : ∀ i j : Fin N, j ≤ i → i.val ≤ j.val+q → |V.transpose i j| ≤ K :=
    fun i j h1 h2 => hV j i h1 h2
  have hh := lower_variation_near_bound U.transpose V.transpose dinv hM hD hK
    hUt (fun i j => hUM j i) hd hVt j i hij hji
  have hpart : lowerPart V.transpose = (upperPart V).transpose := by
    ext i j
    simp only [lowerPart,upperPart,Matrix.transpose_apply]
  rw [hpart] at hh
  have he : U.transpose*(upperPart V).transpose*Matrix.diagonal dinv =
      (Matrix.diagonal dinv*upperPart V*U).transpose := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.diagonal_transpose]
    exact Matrix.mul_assoc _ _ _
  rw [he] at hh
  exact hh

end BTP.Stability.BandLDU
