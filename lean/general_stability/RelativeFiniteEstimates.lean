import FiniteInverseEstimate
import RelativePrefixBounds

/-! Finite-section relative LDU estimates after independent diagonal
scalings of the lower and upper sides. The constants do not depend on
the section size or on the magnitudes of the diagonal entries. -/
noncomputable section
namespace BTP.RelativeStability
open Finset Matrix BTP.Stability.BandLDU

variable {N : ℕ}

local instance : PartialOrder (Mat N) := inferInstanceAs (PartialOrder (Fin N → Fin N → ℝ))

def absMatrix (A : Mat N) : Mat N := fun i j => |A i j|

theorem absMatrix_mul_le (A B : Mat N) :
    absMatrix (A*B) ≤ absMatrix A*absMatrix B := by
  intro i j
  simp only [absMatrix,Matrix.mul_apply]
  exact (abs_sum_le_sum_abs _ _).trans_eq (by simp_rw [abs_mul])

theorem matrix_mul_mono (A B C D : Mat N) (hAB : A ≤ B) (hCD : C ≤ D)
    (hC : 0 ≤ C) (hB : 0 ≤ B) : A*C ≤ B*D := by
  intro i j
  simp only [Matrix.mul_apply]
  exact sum_le_sum fun k _ => mul_le_mul (hAB i k) (hCD k j) (hC k j) (hB i k)

theorem matrix_mul_nonneg (A B : Mat N) (hA : 0 ≤ A) (hB : 0 ≤ B) : 0 ≤ A*B := by
  intro i j
  change 0 ≤ ∑ k, A i k*B k j
  exact sum_nonneg fun k _ => mul_nonneg (hA i k) (hB k j)

theorem matrix_lower_mul {A B : Mat N} (hA : Lower A) (hB : Lower B) : Lower (A*B) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply sum_eq_zero
  intro k _
  by_cases hik : i < k
  · rw [hA i k hik,zero_mul]
  · rw [hB k j (lt_of_le_of_lt (le_of_not_gt hik) hij),mul_zero]

theorem matrix_upper_mul {A B : Mat N} (hA : Upper A) (hB : Upper B) : Upper (A*B) := by
  intro i j hji
  rw [Matrix.mul_apply]
  apply sum_eq_zero
  intro k _
  by_cases hki : k < i
  · rw [hA i k hki,zero_mul]
  · rw [hB k j (lt_of_lt_of_le hji (le_of_not_gt hki)),mul_zero]

/-- A triangular central product is bounded by the cumulative diagonal
sum, rather than by a bound on individual diagonal entries. -/
theorem central_product_bound (A B : Mat N) (d : Fin N → ℝ)
    (hA : Lower A) (hB : Upper B) (_hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hd : ∀ i,0 ≤ d i) {C D Z : ℝ} (hC : 0 ≤ C) (_hD : 0 ≤ D)
    (ha : ∀ i j,A i j ≤ C) (hb : ∀ i j,B i j ≤ D)
    (hz : ∀ j,∑ k ∈ Iic j,d k ≤ Z*d j) (i j : Fin N) :
    (A*Matrix.diagonal d*B) i j ≤ C*D*Z*d (min i j) := by
  have he : (A*Matrix.diagonal d*B) i j =
      ∑ k ∈ Iic (min i j),A i k*d k*B k j := by
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal]
    symm
    apply sum_subset (subset_univ _)
    intro k _ hk
    have hnot : ¬k ≤ min i j := by simpa using hk
    rcases lt_or_ge i k with hik | hki
    · rw [hA i k hik,zero_mul,zero_mul]
    · have hjk : j < k := by
        by_contra hn
        exact hnot (le_min hki (le_of_not_gt hn))
      rw [hB k j hjk,mul_zero]
  rw [he]
  calc
    _ ≤ ∑ k ∈ Iic (min i j),C*D*d k := by
      apply sum_le_sum
      intro k _
      have hh := mul_le_mul (mul_le_mul_of_nonneg_right (ha i k) (hd k)) (hb k j)
        (hB0 k j) (mul_nonneg hC (hd k))
      nlinarith only [hh]
    _ = C*D*(∑ k ∈ Iic (min i j),d k) := by rw [mul_sum]
    _ ≤ C*D*(Z*d (min i j)) :=
      mul_le_mul_of_nonneg_left (hz (min i j)) (mul_nonneg hC _hD)
    _ = _ := by ring

/-- Relative input errors are controlled by the two positive
convolutions of triangular inverses with their original factors. -/
theorem relative_sandwich_bound (L U Li Ui E : Mat N) (d : Fin N → ℝ)
    (hL : Lower L) (hU : Upper U) (hLi : Lower Li) (hUi : Upper Ui)
    (hL0 : 0 ≤ L) (hU0 : 0 ≤ U) (hd : ∀ i,0 ≤ d i)
    {ε C D Z : ℝ} (heps : 0 ≤ ε) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hE : absMatrix E ≤ ε • (L*Matrix.diagonal d*U))
    (hc : ∀ i j,(absMatrix Li*L) i j ≤ C)
    (hu : ∀ i j,(U*absMatrix Ui) i j ≤ D)
    (hz : ∀ j,∑ k ∈ Iic j,d k ≤ Z*d j) (i j : Fin N) :
    |(Li*E*Ui) i j| ≤ ε*C*D*Z*d (min i j) := by
  have hLi0 : 0 ≤ absMatrix Li := fun i j => abs_nonneg _
  have hUi0 : 0 ≤ absMatrix Ui := fun i j => abs_nonneg _
  have hE0 : 0 ≤ absMatrix E := fun i j => abs_nonneg _
  have hT0 : 0 ≤ L*Matrix.diagonal d*U :=
    matrix_mul_nonneg _ _ (matrix_mul_nonneg _ _ hL0 (by
      intro i j; by_cases h : i=j
      · subst j; simpa using hd i
      · simp [Matrix.diagonal,h])) hU0
  have hbound : absMatrix (Li*E*Ui) ≤
      ε • ((absMatrix Li*L)*Matrix.diagonal d*(U*absMatrix Ui)) := by
    calc
      _ ≤ absMatrix (Li*E)*absMatrix Ui := absMatrix_mul_le _ _
      _ ≤ (absMatrix Li*absMatrix E)*absMatrix Ui :=
        matrix_mul_mono _ _ _ _ (absMatrix_mul_le _ _) le_rfl hUi0
          (matrix_mul_nonneg _ _ hLi0 hE0)
      _ ≤ (absMatrix Li*(ε • (L*Matrix.diagonal d*U)))*absMatrix Ui :=
        matrix_mul_mono _ _ _ _ (matrix_mul_mono _ _ _ _ le_rfl hE hE0 hLi0)
          le_rfl hUi0 (matrix_mul_nonneg _ _ hLi0 (by
            intro i j; exact mul_nonneg heps (hT0 i j)))
      _ = _ := by simp only [Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_assoc]
  have hLiL : Lower (absMatrix Li*L) := matrix_lower_mul
    (fun i j hij => by simp [absMatrix,hLi i j hij]) hL
  have hUUi : Upper (U*absMatrix Ui) := matrix_upper_mul hU
    (fun i j hij => by simp [absMatrix,hUi i j hij])
  have hb := central_product_bound (absMatrix Li*L) (U*absMatrix Ui) d
    hLiL hUUi (matrix_mul_nonneg _ _ hLi0 hL0) (matrix_mul_nonneg _ _ hU0 hUi0)
    hd hC hD hc hu hz i j
  have hh := (hbound i j).trans (mul_le_mul_of_nonneg_left hb heps)
  simpa only [absMatrix,smul_eq_mul,mul_assoc] using hh


theorem finite_sum_forward_band_le (f : Fin N → ℝ) (j : Fin N) (p : ℕ)
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ k,f k ≤ B)
    (hz : ∀ k,k < j ∨ j.val+p < k.val → f k=0) :
    ∑ k,f k ≤ (p+1 : ℝ)*B := by
  let t : Fin N := ⟨min (j.val+p) (N-1),by have := j.isLt; omega⟩
  have he : ∑ k,f k = ∑ k ∈ Icc j t,f k := by
    symm
    apply sum_subset (subset_univ _)
    intro k _ hk
    have hn : ¬(j ≤ k ∧ k ≤ t) := by simpa using hk
    apply hz
    by_cases hkj : k < j
    · exact Or.inl hkj
    · right
      have hkt : t < k := lt_of_not_ge (fun h => hn ⟨le_of_not_gt hkj,h⟩)
      have hval : min (j.val+p) (N-1) < k.val := hkt
      have := k.isLt
      omega
  rw [he]
  calc
    _ ≤ ∑ k ∈ Icc j t,B := sum_le_sum fun k _ => hf k
    _ = ((Icc j t).card : ℝ)*B := by simp
    _ ≤ (p+1 : ℝ)*B := by
      apply mul_le_mul_of_nonneg_right _ hB
      have hc : (Icc j t).card ≤ p+1 := by
        rw [Fin.card_Icc]
        dsimp [t]
        omega
      exact_mod_cast hc

theorem triangular_convolution_bound (Q L : Mat N) (p : ℕ)
    (hL : Lower L) (hband : LowerBandwidth p L)
    (_hQ0 : 0 ≤ Q) (hL0 : 0 ≤ L) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hQ : ∀ i j,Q i j ≤ A) (hLM : ∀ i j,L i j ≤ B) (i j : Fin N) :
    (Q*L) i j ≤ (p+1 : ℝ)*A*B := by
  rw [Matrix.mul_apply]
  have hh := finite_sum_forward_band_le (fun k => Q i k*L k j) j p (mul_nonneg hA hB)
    (fun k => mul_le_mul (hQ i k) (hLM k j) (hL0 k j) hA) (by
      intro k hk
      rcases hk with hk | hk
      · rw [hL k j hk,mul_zero]
      · rw [hband k j hk,mul_zero])
  simpa only [mul_assoc] using hh

/-- The original product is comparable to d_j L_ij on its lower side. -/
theorem relative_original_lower_bound (L U : Mat N) (d : Fin N → ℝ)
    (hU : Upper U) (hL0 : 0 ≤ L) (hU0 : 0 ≤ U) (hd : ∀ i,0 ≤ d i)
    {A K Z : ℝ} (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hu : ∀ i j,U i j ≤ A)
    (hprefix : ∀ i j k,k ≤ j → j ≤ i → L i k ≤ K*L i j)
    (hz : ∀ j,∑ k ∈ Iic j,d k ≤ Z*d j) (i j : Fin N) (hji : j ≤ i) :
    (L*Matrix.diagonal d*U) i j ≤ K*A*Z*d j*L i j := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal]
  have he : (∑ k,L i k*d k*U k j)=∑ k ∈ Iic j,L i k*d k*U k j := by
    symm
    apply sum_subset (subset_univ _)
    intro k _ hk
    rw [hU k j (by simpa using hk),mul_zero]
  rw [he]
  calc
    _ ≤ ∑ k ∈ Iic j,K*L i j*A*d k := by
      apply sum_le_sum
      intro k hk
      have hh := mul_le_mul (mul_le_mul_of_nonneg_right
        (hprefix i j k (mem_Iic.mp hk) hji) (hd k)) (hu k j)
        (hU0 k j) (mul_nonneg (mul_nonneg hK (hL0 i j)) (hd k))
      nlinarith only [hh]
    _ = (K*L i j*A)*(∑ k ∈ Iic j,d k) := by rw [mul_sum]
    _ ≤ (K*L i j*A)*(Z*d j) := mul_le_mul_of_nonneg_left (hz j) (by
      exact mul_nonneg (mul_nonneg hK (hL0 i j)) hA)
    _ = _ := by ring

/-- The lower inverse formula must be estimated in its cancellation
form. Bounding L times the strictly lower part directly would lose the
relative scale of the desired matrix entry. -/
theorem relative_lower_cancellation_bound (L Li Ui E : Mat N) (d : Fin N → ℝ)
    (hLLi : L*Li=1) (hUi : Upper Ui) (hL0 : 0 ≤ L) (hd : ∀ i,0 < d i)
    {ε B C K Z : ℝ} (heps : 0 ≤ ε) (hB : 0 ≤ B) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hUiB : ∀ i j,|Ui i j| ≤ B)
    (hE : ∀ i j,j ≤ i → |E i j| ≤ ε*C*d j*L i j)
    (hV : ∀ i j,i ≤ j → |(Li*E*Ui) i j| ≤ ε*C*d i)
    (hprefix : ∀ i j k,k ≤ j → j ≤ i → L i k ≤ K*L i j)
    (hz : ∀ j,∑ k ∈ Iic j,d k ≤ Z*d j)
    (i j : Fin N) (hji : j ≤ i) :
    |(L*lowerPart (Li*E*Ui)*Matrix.diagonal (fun k => (d k)⁻¹)) i j| ≤
      ε*C*K*(B+1)*Z*L i j := by
  let V := Li*E*Ui
  have hLij : 0 ≤ L i j := hL0 i j
  have hid : L*lowerPart V=E*Ui-L*(diagPart V+upperPart V) := by
    have ht : L*V=E*Ui := by dsimp [V]; rw [←Matrix.mul_assoc,←Matrix.mul_assoc,hLLi,Matrix.one_mul]
    have hs := congrArg (fun A : Mat N => L*A) (parts_sum V)
    rw [ht,Matrix.mul_add,Matrix.mul_add] at hs
    rw [Matrix.mul_add]
    exact eq_sub_iff_add_eq.mpr (by simpa only [add_assoc] using hs)
  have hp (k : Fin N) (hk : k ≤ j) :
      |E i k*Ui k j| ≤ ε*C*K*L i j*B*d k := by
    have hLik : 0 ≤ L i k := hL0 i k
    have hdk := hd k
    have hh := mul_le_mul (hE i k (hk.trans hji)) (hUiB k j) (abs_nonneg _) (by positivity)
    rw [abs_mul]
    calc
      _ ≤ (ε*C*d k*L i k)*B := hh
      _ ≤ (ε*C*d k*(K*L i j))*B :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hprefix i j k hk hji) (by positivity)) hB
      _ = _ := by ring
  have hvp (k : Fin N) (hk : k ≤ j) :
      |L i k*(diagPart V+upperPart V) k j| ≤ ε*C*K*L i j*d k := by
    have hdk := hd k
    have he : (diagPart V+upperPart V) k j=V k j := by
      by_cases heq : k=j
      · subst j; simp [diagPart,upperPart]
      · simp [diagPart,upperPart,heq,lt_of_le_of_ne hk heq]
    rw [he,abs_mul,abs_of_nonneg (hL0 i k)]
    calc
      _ ≤ L i k*(ε*C*d k) := mul_le_mul_of_nonneg_left (hV k j hk) (hL0 i k)
      _ ≤ (K*L i j)*(ε*C*d k) := mul_le_mul_of_nonneg_right (hprefix i j k hk hji) (by positivity)
      _ = _ := by ring
  have hs1 : |(E*Ui) i j| ≤ ε*C*K*L i j*B*(Z*d j) := by
    rw [Matrix.mul_apply]
    have he : (∑ k,E i k*Ui k j)=∑ k ∈ Iic j,E i k*Ui k j := by
      symm; apply sum_subset (subset_univ _)
      intro k _ hk
      rw [hUi k j (by simpa using hk),mul_zero]
    rw [he]
    apply (abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ k ∈ Iic j,ε*C*K*L i j*B*d k := sum_le_sum fun k hk => hp k (mem_Iic.mp hk)
      _ = (ε*C*K*L i j*B)*(∑ k ∈ Iic j,d k) := by rw [mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hz j) (by positivity)
  have hs2 : |(L*(diagPart V+upperPart V)) i j| ≤ ε*C*K*L i j*(Z*d j) := by
    rw [Matrix.mul_apply]
    have he : (∑ k,L i k*(diagPart V+upperPart V) k j)=
        ∑ k ∈ Iic j,L i k*(diagPart V+upperPart V) k j := by
      symm; apply sum_subset (subset_univ _)
      intro k _ hk
      rw [diag_upper_upper V k j (by simpa using hk),mul_zero]
    rw [he]
    apply (abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ k ∈ Iic j,ε*C*K*L i j*d k := sum_le_sum fun k hk => hvp k (mem_Iic.mp hk)
      _ = (ε*C*K*L i j)*(∑ k ∈ Iic j,d k) := by rw [mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hz j) (by positivity)
  change |(L*lowerPart V*Matrix.diagonal (fun k => (d k)⁻¹)) i j| ≤ _
  rw [Matrix.mul_diagonal,abs_mul,abs_of_pos (inv_pos.mpr (hd j))]
  have hh : |(L*lowerPart V) i j| ≤ ε*C*K*(B+1)*Z*L i j*d j := by
    rw [hid,Matrix.sub_apply]
    exact (abs_sub _ _).trans ((add_le_add hs1 hs2).trans_eq (by ring))
  have hh' := mul_le_mul_of_nonneg_right hh (inv_pos.mpr (hd j)).le
  simpa only [mul_assoc,mul_inv_cancel₀ (ne_of_gt (hd j)),mul_one] using hh'


theorem relative_upper_cancellation_bound (U Li Ui E : Mat N) (d : Fin N → ℝ)
    (hUiU : Ui*U=1) (hLi : Lower Li) (hU0 : 0 ≤ U) (hd : ∀ i,0 < d i)
    {ε B C K Z : ℝ} (heps : 0 ≤ ε) (hB : 0 ≤ B) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hLiB : ∀ i j,|Li i j| ≤ B)
    (hE : ∀ i j,i ≤ j → |E i j| ≤ ε*C*d i*U i j)
    (hV : ∀ i j,j ≤ i → |(Li*E*Ui) i j| ≤ ε*C*d j)
    (hprefix : ∀ i j k,k ≤ i → i ≤ j → U k j ≤ K*U i j)
    (hz : ∀ j,∑ k ∈ Iic j,d k ≤ Z*d j)
    (i j : Fin N) (hij : i ≤ j) :
    |(Matrix.diagonal (fun k => (d k)⁻¹)*upperPart (Li*E*Ui)*U) i j| ≤
      ε*C*K*(B+1)*Z*U i j := by
  have htr : Ui.transpose*E.transpose*Li.transpose=(Li*E*Ui).transpose := by
    rw [Matrix.transpose_mul,Matrix.transpose_mul,Matrix.mul_assoc]
  have hh := relative_lower_cancellation_bound U.transpose Ui.transpose Li.transpose E.transpose d
    (by rw [←Matrix.transpose_mul,hUiU,Matrix.transpose_one])
    (fun i j hij => hLi j i hij) (fun i j => hU0 j i) hd heps hB hC hK
    (fun i j => hLiB j i) (fun i j h => hE j i h)
    (by intro i j h; rw [htr]; exact hV j i h)
    (fun i j k hkj hji => hprefix j i k hkj hji) hz j i hij
  rw [htr] at hh
  have he : lowerPart (Li*E*Ui).transpose=(upperPart (Li*E*Ui)).transpose := by
    ext i j
    simp [lowerPart,upperPart]
  rw [he] at hh
  have hp : U.transpose*(upperPart (Li*E*Ui)).transpose*Matrix.diagonal (fun k => (d k)⁻¹)=
      (Matrix.diagonal (fun k => (d k)⁻¹)*upperPart (Li*E*Ui)*U).transpose := by
    rw [Matrix.transpose_mul,Matrix.transpose_mul,Matrix.diagonal_transpose,Matrix.mul_assoc]
  rw [hp] at hh
  exact hh

#print axioms relative_upper_cancellation_bound
#print axioms relative_lower_cancellation_bound
#print axioms relative_sandwich_bound
end BTP.RelativeStability
