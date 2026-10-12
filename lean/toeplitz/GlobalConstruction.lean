import PlannedColumns

/-! # Repeated extraction gives one positive factorization in all rows -/
open Matrix Finset Filter
open scoped Topology
noncomputable section
namespace BTP.SemiInfinite
open Extraction InverseBounds

theorem outer_positive_of_windows {m : ℕ} (hm : 0 < m) {F R : NatMatrix}
    (hF : ∀ d, UnitLower d F) (hb : ∀ d, Bandwidth d m F)
    (hR : SignedInverse F R)
    (hW : ∀ n, 0 < windowDet m (fun t j => R t j.val) n) :
    ∀ n, m ≤ n → 0 < F n (n - m) := by
  intro n hn
  have he := inverse_window_det hF hR (m - 1) (n - m)
    (by simpa only [show m - 1 + 1 = m by omega] using hb (n - m + (m - 1) + 2))
  rw [show m - 1 + 1 = m by omega, show n - m + (m - 1) + 1 = n by omega] at he
  have hp := hW (n - m + 1)
  rw [he] at hp
  exact (mul_pos_iff_of_pos_right (hW (n - m))).mp hp

/-- All conclusions needed to repeat extraction, including the new signed inverse. -/
theorem positive_extraction {m : ℕ} (hm : 2 ≤ m) (F R : NatMatrix) (θ : ℕ → ℝ)
    (hF : ∀ d, UnitLower d F) (hb : ∀ d, Bandwidth d m F)
    (hext : ∀ n, m ≤ n → 0 < F n (n - m)) (hR : SignedInverse F R)
    (hθ : ∀ n, 0 < n → n < m → 0 < θ n)
    (hW : ∀ n, 0 < windowDet (m - 1) (extractionColumns R θ m) n) :
    ∃ a : ℕ → ℝ, ∃ H S : NatMatrix,
      (∀ n, 0 < n → 0 < a n) ∧
      (∀ n, 0 < n → n < m → a n = θ n) ∧
      (∀ d, UnitLower d H) ∧ (∀ d, Bandwidth d (m - 1) H) ∧
      (∀ n, m - 1 ≤ n → 0 < H n (n - (m - 1))) ∧
      SignedInverse H S ∧
      (∀ n j, S n j = R n j - a (j + 1) * R n (j + 1)) ∧
      (∀ d, bidiagonal d a * finiteMatrix d H = finiteMatrix d F) := by
  have hφ := extraction_recurrence_positive hm F R θ hF hb hext hR hθ hW
  let φ := canonicalSequence m (by omega) F θ
  let a := fun n => φ (n - 1) / φ n
  let H := remainder a F
  let S := removedInverse R a
  have ha : ∀ n, 0 < n → n < m → a n = θ n :=
    initial_ratios m (by omega) θ φ (fun n hn hnm => (hθ n hn hnm).ne')
      (canonical_initial m (by omega) F θ)
  have hH : ∀ d, UnitLower d H := fun d => remainder_unit d a F (hF d)
  have hS : SignedInverse H S := signedInverse_remainder hF hR a
  have hbH : ∀ d, Bandwidth d (m - 1) H := by
    intro d
    apply remainder_bandwidth d m (by omega) a φ F (hb d)
      (quotient_relation d φ (fun n _ => (hφ n).ne')) (fun n _ => (hφ n).ne')
    exact canonical_recurrence d m (by omega) F θ (fun n hn _ => (hext n hn).ne')
  have hwS : ∀ n, 0 < windowDet (m - 1) (fun t j => S t j.val) n := by
    intro n
    convert hW n using 1
    unfold windowDet
    congr 1
    ext i j
    dsimp [S, removedInverse, extractionColumns]
    rw [ha (j.val + 1) (by omega) (by omega)]
    ring
  refine ⟨a, H, S, (fun n _ => div_pos (hφ _) (hφ _)), ha, hH, hbH,
    outer_positive_of_windows (by omega) hH hbH hS hwS, hS, ?_, ?_⟩
  · intro n j; dsimp [S, removedInverse]; ring
  · intro d; exact remainder_factorization d a F (hF d)

theorem lowerProduct_congr {a b : Entries} {p : ℕ}
    (h : ∀ j < p, a j = b j) (d : ℕ) : lowerProduct d a p = lowerProduct d b p := by
  induction p with
  | zero => rfl
  | succ p ih =>
    rw [lowerProduct, lowerProduct, h p (by omega), ih (fun j hj => h j (by omega))]

theorem bandwidth_one_factor (F : NatMatrix) (hF : ∀ d, UnitLower d F)
    (hb : ∀ d, Bandwidth d 1 F) (d : ℕ) :
    bidiagonal d (fun n => F n (n - 1)) = finiteMatrix d F := by
  ext i j
  simp only [bidiagonal, Matrix.add_apply, Matrix.one_apply, Matrix.of_apply, finiteMatrix]
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl, ite_eq_right (show ¬ i.val = i.val + 1 by omega), add_zero]
    exact ((hF d).1 i.val i.isLt).symm
  · rw [ite_eq_right hij, zero_add]
    by_cases hs : i.val = j.val + 1
    · rw [ite_eq_left hs, show i.val - 1 = j.val by omega]
    · rw [ite_eq_right hs]
      have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
      by_cases hu : i.val < j.val
      · exact ((hF d).2 i.val i.isLt j.val j.isLt hu).symm
      · exact (hb d i.val i.isLt j.val j.isLt (by omega)).symm

/-- The induction preserves equality with the original planned inverse columns.
It therefore uses the same finite list of initial entries at every stage. -/
theorem construct_from_planned_windows (p : ℕ) (Q : NatMatrix) (u : Parameters p)
    (hu : ∀ c, 0 < u c)
    (hW : ∀ l ≤ p, ∀ n, 0 < plannedWindow Q p u l n) :
    ∀ m, 0 < m → ∀ l, m + l = p → ∀ F R : NatMatrix,
      (∀ d, UnitLower d F) → (∀ d, Bandwidth d m F) →
      (∀ n, m ≤ n → 0 < F n (n - m)) → SignedInverse F R →
      (∀ n j, j < m → R n j = plannedInverse Q p u l n j) →
      ∃ b : Entries, Positive m b ∧
        (∀ j < m, ∀ n, 0 < n → n ≤ j → b j n = freeValue p u j n) ∧
        (∀ d, lowerProduct d b m = finiteMatrix d F) := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hm l hml F R hF hb hext hR hcols
    by_cases hm1 : m = 1
    · subst m
      refine ⟨fun _ n => F n (n - 1), ?_, ?_, ?_⟩
      · intro j hj n hn; exact hext n hn
      · intro j hj n hn hnj; omega
      · intro d
        rw [lowerProduct, lowerProduct, Matrix.mul_one]
        exact bandwidth_one_factor F hF hb d
    · have hm2 : 2 ≤ m := by omega
      let θ := freeValue p u (m - 1)
      have hθ : ∀ n, 0 < n → n < m → 0 < θ n := by
        intro n hn hnm
        exact freeValue_pos p (m - 1) n (by omega) hn (by omega) u hu
      have hecols : ∀ n (j : Fin (m - 1)),
          extractionColumns R θ m n j = plannedInverse Q p u (l + 1) n j.val := by
        intro n j
        rw [plannedInverse_succ]
        unfold extractionColumns θ
        rw [hcols n j.val (by omega), hcols n (j.val + 1) (by omega),
          show p - (l + 1) = m - 1 by omega]
      have hWe : ∀ n, 0 < windowDet (m - 1) (extractionColumns R θ m) n := by
        intro n
        have hw := hW (l + 1) (by omega) n
        unfold plannedWindow at hw
        rw [show p - (l + 1) = m - 1 by omega] at hw
        convert hw using 1
        unfold windowDet
        congr 1
        ext i j
        exact hecols (n + i.val) j
      obtain ⟨a, H, S, ha, hainit, hH, hbH, hextH, hS, hScols, hprod⟩ :=
        positive_extraction hm2 F R θ hF hb hext hR hθ hWe
      have hnext : ∀ n j, j < m - 1 → S n j = plannedInverse Q p u (l + 1) n j := by
        intro n j hj
        rw [hScols, hainit (j + 1) (by omega) (by omega)]
        exact hecols n ⟨j, hj⟩
      obtain ⟨b, hbpos, hbinit, hbprod⟩ := ih (m - 1) (by omega) (by omega)
        (l + 1) (by omega) H S hH hbH hextH hS hnext
      let c : Entries := fun j n => if j = m - 1 then a n else b j n
      have hcb : ∀ j < m - 1, c j = b j := by
        intro j hj; funext n; simp [c, show j ≠ m - 1 by omega]
      have hca : c (m - 1) = a := by funext n; simp [c]
      refine ⟨c, ?_, ?_, ?_⟩
      · intro j hj n hn
        by_cases he : j = m - 1
        · rw [he, hca]; exact ha n hn
        · rw [hcb j (by omega)]; exact hbpos j (by omega) n hn
      · intro j hj n hn hnj
        by_cases he : j = m - 1
        · subst j; rw [hca]; exact hainit n hn (by omega)
        · rw [hcb j (by omega)]; exact hbinit j (by omega) n hn hnj
      · intro d
        rw [show m = (m - 1) + 1 by omega, lowerProduct, hca,
          lowerProduct_congr hcb d, hbprod d]
        exact hprod d

#print axioms positive_extraction
#print axioms construct_from_planned_windows
end BTP.SemiInfinite
