import RelativeFiniteEstimates

noncomputable section
namespace BTP.RelativeStability
open Finset Matrix BTP.Stability.BandLDU
variable {N : ℕ}
local instance : PartialOrder (Mat N) := inferInstanceAs (PartialOrder (Fin N → Fin N → ℝ))

structure FiniteRelativeControl (p q : ℕ) (L U Li Ui : Mat N) (d : Fin N → ℝ)
    (A B K Z : ℝ) : Prop where
  lowerL : Lower L
  upperU : Upper U
  lowerLi : Lower Li
  upperUi : Upper Ui
  lowerBand : LowerBandwidth p L
  upperBand : UpperBandwidth q U
  nonnegL : 0 ≤ L
  nonnegU : 0 ≤ U
  positiveD : ∀ i,0 < d i
  leftInverse : L*Li=1
  rightInverse : Ui*U=1
  boundL : ∀ i j,L i j ≤ A
  boundU : ∀ i j,U i j ≤ A
  boundLi : ∀ i j,|Li i j| ≤ B
  boundUi : ∀ i j,|Ui i j| ≤ B
  prefixL : ∀ i j k,k ≤ j → j ≤ i → L i k ≤ K*L i j
  prefixU : ∀ i j k,k ≤ i → i ≤ j → U k j ≤ K*U i j
  rowD : ∀ j,∑ k ∈ Iic j,d k ≤ Z*d j

def relativeFiniteConstant (p q : ℕ) (A B K Z : ℝ) : ℝ :=
  let Cv := ((p+1 : ℝ)*B*A)*((q+1 : ℝ)*B*A)*Z
  (Cv+K*A*Z)*K*(B+1)*Z+Cv

theorem relativeFiniteConstant_nonneg (p q : ℕ) (A B K Z : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hK : 0 ≤ K) (hZ : 0 ≤ Z) :
    0 ≤ relativeFiniteConstant p q A B K Z := by unfold relativeFiniteConstant; positivity

theorem finite_relative_inverse_bound {p q : ℕ} (L U Li Ui : Mat N) (d : Fin N → ℝ)
    {A B K Z ε : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hK : 0 ≤ K) (hZ : 0 ≤ Z)
    (h : FiniteRelativeControl p q L U Li Ui d A B K Z)
    (E : Mat N) (heps : 0 ≤ ε)
    (hE : ∀ i j,|E i j| ≤ ε*(L*Matrix.diagonal d*U) i j) :
    (∀ i j,j ≤ i →
      |(L*lowerPart (Li*E*Ui)*Matrix.diagonal (fun k => (d k)⁻¹)) i j| ≤
        ε*relativeFiniteConstant p q A B K Z*L i j) ∧
    (∀ i,|(Li*E*Ui) i i| ≤ ε*relativeFiniteConstant p q A B K Z*d i) ∧
    (∀ i j,i ≤ j →
      |(Matrix.diagonal (fun k => (d k)⁻¹)*upperPart (Li*E*Ui)*U) i j| ≤
        ε*relativeFiniteConstant p q A B K Z*U i j) := by
  let Cv : ℝ := ((p+1 : ℝ)*B*A)*((q+1 : ℝ)*B*A)*Z
  let Ct : ℝ := K*A*Z
  have hCv : 0 ≤ Cv := by dsimp [Cv]; positivity
  have hCt : 0 ≤ Ct := by dsimp [Ct]; positivity
  have hCc : 0 ≤ Cv+Ct := add_nonneg hCv hCt
  have hLi0 : 0 ≤ absMatrix Li := fun i j => abs_nonneg _
  have hUi0 : 0 ≤ absMatrix Ui := fun i j => abs_nonneg _
  have hconvL (i j : Fin N) : (absMatrix Li*L) i j ≤ (p+1 : ℝ)*B*A :=
    triangular_convolution_bound _ _ p h.lowerL h.lowerBand hLi0 h.nonnegL hB hA h.boundLi h.boundL i j
  have hconvU (i j : Fin N) : (U*absMatrix Ui) i j ≤ (q+1 : ℝ)*B*A := by
    have ht : (absMatrix Ui).transpose*U.transpose=(U*absMatrix Ui).transpose := by
      rw [Matrix.transpose_mul]
    have hh := triangular_convolution_bound (absMatrix Ui).transpose U.transpose q
      (fun i j hij => h.upperU j i hij) (fun i j hij => h.upperBand j i hij)
      (fun i j => hUi0 j i) (fun i j => h.nonnegU j i) hB hA
      (fun i j => h.boundUi j i) (fun i j => h.boundU j i) j i
    rw [ht] at hh
    exact hh
  have hV (i j : Fin N) : |(Li*E*Ui) i j| ≤ ε*Cv*d (min i j) := by
    have hh := relative_sandwich_bound L U Li Ui E d h.lowerL h.upperU h.lowerLi h.upperUi
      h.nonnegL h.nonnegU (fun i => (h.positiveD i).le) heps
      (show 0 ≤ (p+1 : ℝ)*B*A by positivity) (show 0 ≤ (q+1 : ℝ)*B*A by positivity)
      hE hconvL hconvU h.rowD i j
    simpa only [Cv,mul_assoc] using hh
  have hTL (i j : Fin N) (hji : j ≤ i) : (L*Matrix.diagonal d*U) i j ≤ Ct*d j*L i j :=
    relative_original_lower_bound L U d h.upperU h.nonnegL h.nonnegU
      (fun k => (h.positiveD k).le) hA hK h.boundU h.prefixL h.rowD i j hji
  have hTU (i j : Fin N) (hij : i ≤ j) : (L*Matrix.diagonal d*U) i j ≤ Ct*d i*U i j := by
    have hh := relative_original_lower_bound U.transpose L.transpose d
      (fun i j hij => h.lowerL j i hij) (fun i j => h.nonnegU j i)
      (fun i j => h.nonnegL j i) (fun k => (h.positiveD k).le) hA hK
      (fun i j => h.boundL j i) (fun i j k hkj hji => h.prefixU j i k hkj hji)
      h.rowD j i hij
    have he : U.transpose*Matrix.diagonal d*L.transpose=(L*Matrix.diagonal d*U).transpose := by
      rw [Matrix.transpose_mul,Matrix.transpose_mul,Matrix.diagonal_transpose,Matrix.mul_assoc]
    rw [he] at hh
    exact hh
  have hsmall : (Cv+Ct)*K*(B+1)*Z ≤ relativeFiniteConstant p q A B K Z := by
    change (Cv+Ct)*K*(B+1)*Z ≤ (Cv+Ct)*K*(B+1)*Z+Cv
    exact le_add_of_nonneg_right hCv
  have hdiag : Cv ≤ relativeFiniteConstant p q A B K Z := by
    change Cv ≤ (Cv+Ct)*K*(B+1)*Z+Cv
    exact le_add_of_nonneg_left (by positivity)
  refine ⟨?_,?_,?_⟩
  · intro i j hji
    have he (i j : Fin N) (hji : j ≤ i) : |E i j| ≤ ε*(Cv+Ct)*d j*L i j := by
      have hLij : 0 ≤ L i j := h.nonnegL i j
      calc
        _ ≤ ε*(Ct*d j*L i j) := (hE i j).trans (mul_le_mul_of_nonneg_left (hTL i j hji) heps)
        _ ≤ ε*((Cv+Ct)*d j*L i j) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCv)
            (h.positiveD j).le) hLij) heps
        _ = _ := by ring
    have hv (i j : Fin N) (hij : i ≤ j) : |(Li*E*Ui) i j| ≤ ε*(Cv+Ct)*d i := by
      have hh := hV i j
      rw [min_eq_left hij] at hh
      exact hh.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hCt) heps) (h.positiveD i).le)
    have hh := relative_lower_cancellation_bound L Li Ui E d h.leftInverse h.upperUi h.nonnegL
      h.positiveD heps hB hCc hK h.boundUi he hv h.prefixL h.rowD i j hji
    have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsmall heps) (h.nonnegL i j)
    exact hh.trans (by simpa only [mul_assoc] using hm)
  · intro i
    have hh := hV i i
    rw [min_self] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdiag heps) (h.positiveD i).le)
  · intro i j hij
    have he (i j : Fin N) (hij : i ≤ j) : |E i j| ≤ ε*(Cv+Ct)*d i*U i j := by
      have hUij : 0 ≤ U i j := h.nonnegU i j
      calc
        _ ≤ ε*(Ct*d i*U i j) := (hE i j).trans (mul_le_mul_of_nonneg_left (hTU i j hij) heps)
        _ ≤ ε*((Cv+Ct)*d i*U i j) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCv)
            (h.positiveD i).le) hUij) heps
        _ = _ := by ring
    have hv (i j : Fin N) (hji : j ≤ i) : |(Li*E*Ui) i j| ≤ ε*(Cv+Ct)*d j := by
      have hh := hV i j
      rw [min_eq_right hji] at hh
      exact hh.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hCt) heps) (h.positiveD j).le)
    have hh := relative_upper_cancellation_bound U Li Ui E d h.rightInverse h.lowerLi h.nonnegU
      h.positiveD heps hB hCc hK h.boundLi he hv h.prefixU h.rowD i j hij
    have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsmall heps) (h.nonnegU i j)
    exact hh.trans (by simpa only [mul_assoc] using hm)

#print axioms finite_relative_inverse_bound
end BTP.RelativeStability
