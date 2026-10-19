import BoundedLDUInverse
import FullBandStability

/-! The finite-section data used by the Banach inverse construction are
realized by actual products of positive bidiagonal matrices. -/
noncomputable section
open Matrix Finset
open scoped BigOperators
namespace BTP.Stability.BandLDU
open BTP BTP.InverseBounds BTP.SemiInfinite BTP.GeneralStability

theorem actual_lower (a : Entries) (p N : ℕ) : Lower (lowerProduct N a p) := by
  intro i j hij
  rw [lowerProduct_entry]
  simp [show ¬ j.val  ≤  i.val by exact not_le.mpr hij]

theorem actual_inverse_lower (a : Entries) (p N : ℕ) : Lower ((lowerProduct N a p)⁻¹) := by
  have he : (lowerProduct N a p)⁻¹=checker (qProduct N a p) := by
    rw [qProduct_signed_inverse, checker_twice]
  rw [he]
  intro i j hij
  rw [checker_entry, inverseEntries_finite, inverseEntries_upper a p _ _ hij]
  ring

theorem actual_lower_coherent (a : Entries) (p N : ℕ) :
    principal (lowerProduct (N+1) a p)=lowerProduct N a p := by
  ext i j
  change lowerProduct (N+1) a p i.castSucc j.castSucc=lowerProduct N a p i j
  rw [lowerProduct_entry, lowerProduct_entry]
  rfl

theorem actual_lower_band (a : Entries) (p N : ℕ) : LowerBandwidth p (lowerProduct N a p) := by
  intro i j hij
  rw [lowerProduct_entry]
  rw [ite_eq_left (by omega), entry_band a p i.val (i.val-j.val) (by omega)]

theorem actual_upper_band (b : Entries) (q N : ℕ) :
    UpperBandwidth q ((lowerProduct N b q).transpose) := by
  intro i j hij
  exact actual_lower_band b q N j i hij

def actualData (a b : Entries) (p q : ℕ) (d : ℕ → ℝ) (hd : ∀ n, d n≠0) : SectionData where
  L := fun N => lowerProduct N a p
  Li := fun N => (lowerProduct N a p)⁻¹
  U := fun N => (lowerProduct N b q).transpose
  Ui := fun N => ((lowerProduct N b q)⁻¹).transpose
  d := d
  d_ne := hd
  lower_L := actual_lower a p
  lower_Li := actual_inverse_lower a p
  upper_U := by intro N i j hij; exact actual_lower b q N j i hij
  upper_Ui := by intro N i j hij; exact actual_inverse_lower b q N j i hij
  Li_L := by
    intro N
    exact Matrix.nonsing_inv_mul _ (by rw [lowerProduct_det]; exact isUnit_one)
  L_Li := by
    intro N
    exact Matrix.mul_nonsing_inv _ (by rw [lowerProduct_det]; exact isUnit_one)
  U_Ui := by
    intro N
    rw [← Matrix.transpose_mul, Matrix.nonsing_inv_mul _
      (by rw [lowerProduct_det]; exact isUnit_one), Matrix.transpose_one]
  Ui_U := by
    intro N
    rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv _
      (by rw [lowerProduct_det]; exact isUnit_one), Matrix.transpose_one]
  L_coherent := actual_lower_coherent a p
  U_coherent := by
    intro N
    ext i j
    exact congrArg (fun M : Mat N => M j i) (actual_lower_coherent b q N)

def actualInverse (a : Entries) (p : ℕ) (n s : ℕ) : ℝ :=
  (-1 : ℝ)^n * inverseEntries a p n s * (-1 : ℝ)^s

theorem actualInverse_finite (a : Entries) (p N : ℕ) (i j : Fin N) :
    actualInverse a p i.val j.val = (lowerProduct N a p)⁻¹ i j := by
  have he : (lowerProduct N a p)⁻¹=checker (qProduct N a p) := by
    rw [qProduct_signed_inverse, checker_twice]
  rw [he, checker_entry, inverseEntries_finite]
  rfl

theorem actualInverse_zero (a : Entries) (p n s : ℕ) (h : n < s) :
    actualInverse a p n s=0 := by
  simp [actualInverse, inverseEntries_upper a p n s h]

theorem actualInverse_abs (a : Entries) (p : ℕ)
    (ha : ∀ k  <  p, ∀ n, 0 < n → 0 ≤ a k n) (n s : ℕ) :
    |actualInverse a p n s|=inverseEntries a p n s := by
  have h := actual_inverse_nonneg a p ha n s
  simp [actualInverse, abs_mul, abs_pow, abs_of_nonneg h]

theorem actual_inverse_last_lower (a : Entries) (p : ℕ)
    (ha : ∀ k < p+1, ∀ n, 0 < n → 0 ≤ a k n) (s k : ℕ) :
    blockProduct (a 0) s k ≤ inverseEntries a (p+1) (s+k) s := by
  induction k with
  | zero => simp [blockProduct_zero, inverseEntries_diagonal]
  | succ k ih =>
    rw [blockProduct_succ, show s+(k+1)=(s+k)+1 by omega, inverseEntries_succ]
    have ht : 0 ≤ inverseEntries (fun i n => a (i+1) n) p (s+k+1) s :=
      actual_inverse_nonneg _ p (fun i hi n hn => ha (i+1) (by omega) n hn) _ _
    have hm := mul_le_mul_of_nonneg_right ih (ha 0 (by omega) (s+k+1) (by omega))
    nlinarith

theorem product_entry_uniform_bound (a : Entries) {A : ℝ} (hA : 0 ≤ A)
    (p : ℕ) (ha : ∀ k  <  p, ∀ n, 0 < n → |a k n| ≤ A)
    (n r : ℕ) (hr : r ≤ n) : |entry a p n r| ≤ (1+A)^p := by
  induction p generalizing n r with
  | zero =>
    simp only [entry, pow_zero]
    split_ifs  <;> norm_num
  | succ p ih =>
    cases r with
    | zero =>
      simp only [entry_zero, abs_one]
      exact one_le_pow₀ (by linarith)
    | succ r =>
      rw [entry]
      have h₁ := ih (fun k hk n hn => ha k (by omega) n hn) n (r+1) hr
      have h₂ := ih (fun k hk n hn => ha k (by omega) n hn) (n-1) r (by omega)
      have h₃ := ha p (by omega) n (by omega)
      calc
        _  ≤  |entry a p n (r+1)|+|a p n*entry a p (n-1) r| := abs_add_le _ _
        _ = |entry a p n (r+1)|+|a p n| * |entry a p (n-1) r| := by rw [abs_mul]
        _  ≤  (1+A)^p+A*(1+A)^p :=
          add_le_add h₁ (mul_le_mul h₃ h₂ (abs_nonneg _) hA)
        _ = (1+A)^(p+1) := by rw [pow_succ]; ring

theorem actual_lower_uniform_bound (a : Entries) {A : ℝ} (hA : 0 ≤ A)
    (p : ℕ) (ha : ∀ k  <  p, ∀ n, 0 < n → |a k n| ≤ A)
    (N : ℕ) (i j : Fin N) : |lowerProduct N a p i j| ≤ (1+A)^p := by
  rw [lowerProduct_entry]
  split_ifs with h
  · exact product_entry_uniform_bound a hA p ha i.val (i.val-j.val) (Nat.sub_le _ _)
  · simpa only [abs_zero] using pow_nonneg (show 0 ≤ 1+A by linarith) p

def actualLowerCoordinates (a : Entries) (p : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (ha : ∀ k  <  p, ∀ n, 0 < n → |a k n| ≤ A) : LowerBand p :=
  fun r => BTP.Stability.ofAbsBound (fun n => entry a p (n+r.val+1) (r.val+1))
    ((1+A)^p) (fun n => product_entry_uniform_bound a hA p ha _ _ (by omega))

theorem actualLowerCoordinates_entry (a : Entries) (p : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (ha : ∀ k  <  p, ∀ n, 0 < n → |a k n| ≤ A) (i j : ℕ) (hji : j < i) :
    bandEntry (actualLowerCoordinates a p A hA ha) i j=entry a p i (i-j) := by
  unfold bandEntry
  split_ifs with h
  · dsimp [actualLowerCoordinates]
    congr 1  <;> omega
  · symm
    apply entry_band
    omega

def actualBase (a b : Entries) (p q : ℕ) (d : Seq) (A : ℝ) (hA : 0 ≤ A)
    (ha : ∀ k  <  p, ∀ n, 0 < n → |a k n| ≤ A)
    (hb : ∀ k  <  q, ∀ n, 0 < n → |b k n| ≤ A) : FullBand p q :=
  (actualLowerCoordinates a p A hA ha, d, actualLowerCoordinates b q A hA hb)

theorem actualBase_lower (a b : Entries) (p q : ℕ) (d : Seq) (A : ℝ) (hA : 0 ≤ A)
    (ha : ∀ k  <  p, ∀ n, 0 < n → |a k n| ≤ A)
    (hb : ∀ k  <  q, ∀ n, 0 < n → |b k n| ≤ A) (N : ℕ) :
    lowerProduct N a p = 1+lowerPart (fullSection (actualBase a b p q d A hA ha hb) N) := by
  ext i j
  by_cases hij : i=j
  · subst j
    simp [lowerProduct_entry, lowerPart]
  · by_cases hji : j < i
    · have hval : i.val≠j.val := fun h => hij (Fin.ext h)
      simp only [lowerProduct_entry, show j.val ≤ i.val from hji.le, ite_true,
        Matrix.add_apply, Matrix.one_apply, hij, ite_false, zero_add, lowerPart, hji,
        fullSection, fullEntry, hval]
      simp only [show j.val < i.val from hji, ite_true]
      exact (actualLowerCoordinates_entry a p A hA ha i.val j.val hji).symm
    · have hval : ¬j.val ≤ i.val := by omega
      simp [lowerProduct_entry, hval, lowerPart, hji, hij]

theorem actualBase_upper (a b : Entries) (p q : ℕ) (d : Seq) (A : ℝ) (hA : 0 ≤ A)
    (ha : ∀ k < p, ∀ n, 0 < n → |a k n| ≤ A)
    (hb : ∀ k < q, ∀ n, 0 < n → |b k n| ≤ A) (N : ℕ) :
    (lowerProduct N b q).transpose =
      1+upperPart (fullSection (actualBase a b p q d A hA ha hb) N) := by
  ext i j
  by_cases hij : i=j
  · subst j
    simp [Matrix.transpose_apply, lowerProduct_entry, upperPart]
  · by_cases hji : i < j
    · have hval : i.val≠j.val := fun h => hij (Fin.ext h)
      simp only [Matrix.transpose_apply, lowerProduct_entry, show i.val ≤ j.val from hji.le,
        ite_true, Matrix.add_apply, Matrix.one_apply, hij, ite_false, zero_add,
        upperPart, hji, fullSection, fullEntry, hval,
        show ¬j.val < i.val from not_lt.mpr hji.le]
      exact (actualLowerCoordinates_entry b q A hA hb j.val i.val hji).symm
    · have hval : ¬i.val ≤ j.val := by omega
      simp [Matrix.transpose_apply, lowerProduct_entry, hval, upperPart, hji, hij]

def identityBand (p q : ℕ) : FullBand p q := (0, 1, 0)

theorem identityBand_section (p q N : ℕ) : fullSection (identityBand p q) N=1 := by
  ext i j
  by_cases hij : i=j
  · subst j; simp [fullSection, identityBand, fullEntry]
  · have hv : i.val≠j.val := fun h => hij (Fin.ext h)
    simp [fullSection, identityBand, fullEntry, hv, bandEntry, hij]

/-- Necessity of the manuscript's joint row bound. Even a bounded solution
of the derivative equation in the identity direction suffices. -/
theorem actual_row_bound_of_identity_solution (a b : Entries) (p q : ℕ)
    (d : ℕ → ℝ) (hd : ∀ n, d n≠0)
    (A : FullBand p q →L[ℝ] FullBand p q)
    (hA : (actualData a b p q d hd).IsDerivative A)
    (F : FullBand p q) (hF : A F=identityBand p q) :
    ∀ n, ∑ s ∈ range (n+1), inverseEntries a p n s*inverseEntries b q n s  ≤  ‖F‖ := by
  intro n
  let N := n+1
  let ii : Fin N := ⟨n, by dsimp [N]; omega⟩
  let S := actualData a b p q d hd
  have he := (hA F N).symm
  rw [hF, identityBand_section] at he
  have hz := variation_identity_row_sum (S.L N) (S.Li N) (S.U N) (S.Ui N)
    (lowerPart (fullSection F N)) (diagPart (fullSection F N)) (upperPart (fullSection F N))
    (fun i j => inverseEntries a p i.val j.val) (fun i j => inverseEntries b q i.val j.val)
    (fun i => d i.val) (fun i => (-1 : ℝ)^i.val)
    (S.Li_L N) (S.U_Ui N) (S.lower_Li N) (S.upper_Ui N)
    (lowerPart_strict _) (diagPart_diag _) (upperPart_strict _)
    (fun i => sign_square i.val)
    (fun i j => (actualInverse_finite a p N i j).symm)
    (by intro i j; dsimp [S,actualData]; rw [← actualInverse_finite]; dsimp [actualInverse]; ring)
    he ii
  simp only [diagPart, Matrix.diagonal_apply_eq] at hz
  change fullEntry F n n = ∑ s : Fin (n+1), inverseEntries a p n s.val*inverseEntries b q n s.val at hz
  rw [Fin.sum_univ_eq_sum_range (fun s => inverseEntries a p n s*inverseEntries b q n s) (n+1)] at hz
  rw [← hz]
  exact (le_abs_self _).trans (fullEntry_abs_le F n n)

end BTP.Stability.BandLDU
