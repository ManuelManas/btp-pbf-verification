import FlagComplement
import CanonicalLowerInverse

open Matrix Finset
noncomputable section
namespace BTP.SemiInfinite
open Extraction InverseBounds

theorem remainder_bandwidth_tail (d r : ℕ) (hr : 0 < r) (a φ : ℕ → ℝ) (G : NatMatrix)
    (hb : Bandwidth d r G) (hrel : RatioRelation d a φ) (hφ : ∀ n, r ≤ n → n < d → φ n ≠ 0)
    (hrec : Recurrence d r G φ) : Bandwidth d (r - 1) (remainder a G) := by
  have hboundary : ∀ k, k + r < d → columnRemainder a G k r = 0 := by
    intro k hk
    have hid := boundary_identity d r a φ G hrel (k + r) (by omega) hk
    rw [hrec (k + r) (by omega) hk, sub_self] at hid
    have he : k + r - r = k := by omega
    rw [he] at hid
    exact (mul_eq_zero.mp hid).resolve_left (hφ (k + r) (by omega) hk)
  have htail : ∀ k t, r ≤ t → k + t < d → columnRemainder a G k t = 0 := by
    intro k t ht
    induction t, ht using Nat.le_induction with
    | base => exact hboundary k
    | succ t ht ih =>
      intro hkt
      rw [columnRemainder, ih (by omega), mul_zero, sub_zero]
      exact hb (k + (t + 1)) hkt k (by omega) (by omega)
  intro n hn k hk hkn
  have hle : k ≤ n := by omega
  rw [remainder, ite_eq_left hle]
  exact htail k (n - k) (by omega) (by omega)


theorem zero_initial_canonical {m : ℕ} (hm : 0 < m) (F : NatMatrix) {n : ℕ}
    (hn : n < m-1) : canonicalSequence m hm F (fun _ => 0) n = 0 := by
  rw [canonical_initial m hm F (fun _ => 0) n (by omega)]
  unfold initialValue
  exact prod_eq_zero (mem_Ico.mpr ⟨le_rfl, hn⟩) rfl

/-- With zero initial entries, the first m-1 inverse columns are unchanged. -/
theorem zero_initial_extraction {m : ℕ} (hm : 2 ≤ m) (F R : NatMatrix)
    (hF : ∀ d, UnitLower d F) (hb : ∀ d, Bandwidth d m F)
    (hext : ∀ n, m ≤ n → 0 < F n (n-m)) (hR : SignedInverse F R)
    (hW : ∀ n, 0 < windowDet (m-1) (fun t j => R t j.val) n) :
    ∃ a : ℕ → ℝ, ∃ H S : NatMatrix,
      (∀ n, n < m → a n = 0) ∧ (∀ n, m ≤ n → 0 < a n) ∧
      (∀ d, UnitLower d H) ∧ (∀ d, Bandwidth d (m-1) H) ∧
      SignedInverse H S ∧ (∀ n j, j < m-1 → S n j = R n j) ∧
      (∀ d, bidiagonal d a * finiteMatrix d H = finiteMatrix d F) := by
  let φ := canonicalSequence m (by omega) F (fun _ => 0)
  have hφ : ∀ n, m-1 ≤ n → 0 < φ n := by
    intro n hn
    have he := extraction_determinant_formula_unrestricted hm F R (fun _ => 0)
      hF hb (fun t ht => (hext t ht).ne') hR (n+1-m)
    have hindex : n+1-m+m-1 = n := by omega
    have he' : windowDet (m-1) (fun t j => R t j.val) (n+1-m) =
        (∏ t ∈ Ico m (n+1-m+m), F t (t-m)) * φ n := by
      simpa only [windowDet, extractionColumns, zero_mul, sub_zero, hindex] using he
    have hp : 0 < ∏ t ∈ Ico m (n+1-m+m), F t (t-m) := by
      apply prod_pos
      intro t ht
      exact hext t (mem_Ico.mp ht).1
    have hw := hW (n+1-m)
    rw [he'] at hw
    exact (mul_pos_iff_of_pos_left hp).mp hw
  let a := fun n => if n < m then 0 else φ (n-1) / φ n
  let H := remainder a F
  let S := removedInverse R a
  have ha0 : ∀ n, n < m → a n = 0 := by intro n hn; simp [a, hn]
  have hapos : ∀ n, m ≤ n → 0 < a n := by
    intro n hn
    simp only [a, ite_eq_right (show ¬ n < m by omega)]
    exact div_pos (hφ (n-1) (by omega)) (hφ n (by omega))
  have hrel : ∀ d, RatioRelation d a φ := by
    intro d n hn hnd
    by_cases hnm : n < m
    · rw [ha0 n hnm]
      change 0 * φ n = canonicalSequence m (by omega) F (fun _ => 0) (n-1)
      rw [zero_initial_canonical (by omega) F (by omega), zero_mul]
    · simp only [a, ite_eq_right hnm]
      exact div_mul_cancel₀ _ (hφ n (by omega)).ne'
  have hH : ∀ d, UnitLower d H := fun d => remainder_unit d a F (hF d)
  have hS : SignedInverse H S := signedInverse_remainder hF hR a
  have hbH : ∀ d, Bandwidth d (m-1) H := by
    intro d
    apply remainder_bandwidth_tail d m (by omega) a φ F (hb d) (hrel d)
      (fun n hn _ => (hφ n (by omega)).ne')
    exact canonical_recurrence d m (by omega) F (fun _ => 0)
      (fun n hn _ => (hext n hn).ne')
  refine ⟨a,H,S,ha0,hapos,hH,hbH,hS,?_,?_⟩
  · intro n j hj
    dsimp [S, removedInverse]
    rw [ha0 (j+1) (by omega)]
    ring
  · intro d
    exact remainder_factorization d a F (hF d)

/-- Construction of the complete Metelmann factorization from positive
consecutive minors of the signed inverse. No factorization is assumed. -/
theorem metelmann_from_inverse_flags (m : ℕ) (hm : 0 < m) (F R : NatMatrix)
    (hF : ∀ d, UnitLower d F) (hb : ∀ d, Bandwidth d m F)
    (hR : SignedInverse F R)
    (hW : ∀ k, 0 < k → k ≤ m → ∀ n, 0 < windowDet k (fun t j => R t j.val) n) :
    ∃ a : Entries, Metelmann m a ∧ ∀ d, lowerProduct d a m = finiteMatrix d F := by
  induction m using Nat.strong_induction_on generalizing F R with
  | h m ih =>
    have hext := outer_positive_of_windows hm hF hb hR (hW m hm le_rfl)
    by_cases hm1 : m = 1
    · subst m
      refine ⟨fun _ n => F n (n-1), ⟨?_,?_⟩,?_⟩
      · intro j hj n hn hnj; omega
      · intro j hj n hn
        exact hext n (by omega)
      · intro d
        rw [lowerProduct, lowerProduct, Matrix.mul_one]
        exact bandwidth_one_factor F hF hb d
    · have hm2 : 2 ≤ m := by omega
      obtain ⟨a,H,S,ha0,hapos,hH,hbH,hS,hcols,hprod⟩ :=
        zero_initial_extraction hm2 F R hF hb hext hR (hW (m-1) (by omega) (by omega))
      have hWS : ∀ k, 0 < k → k ≤ m-1 → ∀ n,
          0 < windowDet k (fun t j => S t j.val) n := by
        intro k hk hkm n
        have he : (fun t (j : Fin k) => S t j.val) = (fun t (j : Fin k) => R t j.val) := by
          funext t j
          exact hcols t j.val (by omega)
        rw [he]
        exact hW k hk (by omega) n
      obtain ⟨b,hbmet,hbprod⟩ := ih (m-1) (by omega) (by omega) H S hH hbH hS hWS
      let c : Entries := fun j n => if j = m-1 then a n else b j n
      have hcb : ∀ j < m-1, c j = b j := by
        intro j hj; funext n; simp [c,show j ≠ m-1 by omega]
      have hca : c (m-1) = a := by funext n; simp [c]
      refine ⟨c,⟨?_,?_⟩,?_⟩
      · intro j hj n hn hnj
        by_cases he : j = m-1
        · rw [he,hca]; exact ha0 n (by omega)
        · rw [hcb j (by omega)]; exact hbmet.1 j (by omega) n hn hnj
      · intro j hj n hnj
        by_cases he : j = m-1
        · rw [he,hca]; exact hapos n (by omega)
        · rw [hcb j (by omega)]; exact hbmet.2 j (by omega) n hnj
      · intro d
        rw [show m = (m-1)+1 by omega, lowerProduct, hca,
          lowerProduct_congr hcb d,hbprod d]
        exact hprod d

#print axioms metelmann_from_inverse_flags

/-- The input is BTP itself, not a pre-existing Metelmann product. -/
theorem metelmann_from_BTP (m : ℕ) (hm : 0 < m) (F : NatMatrix)
    (hF : ∀ d, UnitLower d F) (hb : ∀ d, Bandwidth d m F)
    (hTP : Toeplitz.StrictBandTP m 0 F) :
    ∃ a : Entries, Metelmann m a ∧ ∀ d, lowerProduct d a m = finiteMatrix d F := by
  let R := canonicalLowerInverse F
  have hR : SignedInverse F R := canonicalLowerInverse_signed F hF
  apply metelmann_from_inverse_flags m hm F R hF hb hR
  intro k hk hkm n
  rw [inverse_flag_complement F R hF hR]
  exact hTP (fun i : Fin n => k+i.val) (fun j : Fin n => j.val)
    (by intro i j hij; change i.val < j.val at hij; dsimp; omega)
    (by intro i j hij; exact hij)
    (by intro i; constructor <;> dsimp <;> omega)

#print axioms metelmann_from_BTP
end BTP.SemiInfinite
