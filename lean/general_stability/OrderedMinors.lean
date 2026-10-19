import FormalizedTheorem

/-! # Nonnegative ordered minors, proved by elementary row additions -/
open Matrix Finset
noncomputable section
namespace BTP.SemiInfinite
open InverseBounds

def RowNonnegative {α : Type*} [LinearOrder α] {k : ℕ} (M : Matrix α (Fin k) ℝ) : Prop :=
  ∀ I : Fin k → α, StrictMono I → 0 ≤ (M.submatrix I id).det

theorem rowNonnegative_monotone {α : Type*} [LinearOrder α] {k : ℕ} {M : Matrix α (Fin k) ℝ}
    (hM : RowNonnegative M) (I : Fin k → α) (hI : Monotone I) :
    0 ≤ (M.submatrix I id).det := by
  by_cases hinj : Function.Injective I
  · exact hM I (hI.strictMono_of_injective hinj)
  · obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hinj
    rw [Matrix.det_zero_of_row_eq hne (by funext c; exact congrArg (fun t => M t c) hij)]

theorem rowNonnegative_add_previous {α : Type*} [LinearOrder α] {k : ℕ}
    {M : Matrix α (Fin k) ℝ} (hM : RowNonnegative M) (h s : α)
    (hlo : ∀ x, x < h → x ≤ s) (hhi : s ≤ h)
    {c : ℝ} (hc : 0 ≤ c) : RowNonnegative (M.updateRow h (M h + c • M s)) := by
  intro I hI
  by_cases hex : ∃ i, I i = h
  · obtain ⟨i, hi⟩ := hex
    let A := M.submatrix I id
    have he : (M.updateRow h (M h + c • M s)).submatrix I id =
        A.updateRow i (A i + c • M s) := by
      ext j t
      by_cases hj : j = i
      · subst j; simp [A, hi]
      · have hne : I j ≠ h := by intro e; exact hj (hI.injective (e.trans hi.symm))
        simp [Matrix.submatrix_apply, Matrix.updateRow_ne hne,
          Matrix.updateRow_ne hj, A]
    rw [he, Matrix.det_updateRow_add, Matrix.det_updateRow_smul]
    have hself : A.updateRow i (A i) = A := by ext j t; simp
    rw [hself]
    let I' := Function.update I i s
    have him : Monotone I' := by
      intro j t hjt
      by_cases hj : j = i
      · subst j
        by_cases ht : t = i
        · subst t; exact le_rfl
        · have hlt : i < t := lt_of_le_of_ne hjt (Ne.symm ht)
          have hval := hI hlt
          rw [hi] at hval
          change (Function.update I i s) i ≤ (Function.update I i s) t
          simp only [Function.update_self, Function.update_of_ne ht]
          exact hhi.trans hval.le
      · by_cases ht : t = i
        · subst t
          have hval := hI (lt_of_le_of_ne hjt hj)
          rw [hi] at hval
          change (Function.update I i s) j ≤ (Function.update I i s) i
          simp only [Function.update_of_ne hj, Function.update_self]
          exact hlo (I j) hval
        · change (Function.update I i s) j ≤ (Function.update I i s) t
          simp only [Function.update_of_ne hj, Function.update_of_ne ht]
          exact hI.monotone hjt
    have hreplace : A.updateRow i (M s) = M.submatrix I' id := by
      ext j t
      by_cases hj : j = i <;> simp [A, I', hj]
    rw [hreplace]
    exact add_nonneg (hM I hI) (mul_nonneg hc (rowNonnegative_monotone hM I' him))
  · have he : (M.updateRow h (M h + c • M s)).submatrix I id = M.submatrix I id := by
      ext i j
      exact congrFun (Matrix.updateRow_ne (by intro e; exact hex ⟨i, e⟩)) j
    rw [he]
    exact hM I hI

/-- Minors of the identity are zero or one; order fixes the sign. -/
theorem identity_ordered_minor {α : Type*} [LinearOrder α] {k : ℕ} (I J : Fin k → α)
    (hI : StrictMono I) (hJ : StrictMono J) :
    0 ≤ ((1 : Matrix α α ℝ).submatrix I J).det := by
  by_cases he : I = J
  · subst J
    have hm : (1 : Matrix α α ℝ).submatrix I I = 1 := by
      ext i j
      simp [Matrix.one_apply, hI.injective.eq_iff]
    rw [hm, Matrix.det_one]; norm_num
  · have hex : ∃ i, ∀ j, I i ≠ J j := by
      by_contra h
      push Not at h
      choose f hf using h
      have hfm : StrictMono f := by
        intro i j hij
        apply hJ.lt_iff_lt.mp
        rw [← hf i, ← hf j]
        exact hI hij
      have hid : f = id := hfm.eq_id
      apply he
      funext i
      simpa only [hid, id_eq] using hf i
    obtain ⟨i, hi⟩ := hex
    rw [Matrix.det_eq_zero_of_row_eq_zero i (by intro j; simp [hi j])]

/-- Forward substitution is a sequence of adjacent row additions. -/
theorem rowNonnegative_forward {k : ℕ} (M N : Matrix ℕ (Fin k) ℝ) (c : ℕ → ℝ)
    (hM : RowNonnegative M) (hc : ∀ n, 0 < n → 0 ≤ c n)
    (hzero : N 0 = M 0) (hstep : ∀ n, N (n + 1) = M (n + 1) + c (n + 1) • N n) :
    RowNonnegative N := by
  let P : ℕ → Matrix ℕ (Fin k) ℝ := fun t i => if i ≤ t then N i else M i
  have hbase : P 0 = M := by
    funext i
    by_cases hi : i = 0
    · subst i; simp [P, hzero]
    · simp [P, show ¬ i ≤ 0 by omega]
  have hs : ∀ t, P (t + 1) = (P t).updateRow (t + 1)
      ((P t) (t + 1) + c (t + 1) • (P t) t) := by
    intro t
    funext i j
    by_cases hi : i = t + 1
    · subst i
      simp only [P, Matrix.updateRow, Matrix.of_apply, Function.update_self, le_refl, ite_true,
        show ¬ t + 1 ≤ t by omega, ite_false]
      exact congrFun (hstep t) j
    · rw [Matrix.updateRow_ne hi]
      dsimp [P]
      by_cases hh : i ≤ t
      · simp only [ite_eq_left hh, ite_eq_left (show i ≤ t + 1 by omega)]
      · simp only [ite_eq_right hh, ite_eq_right (show ¬ i ≤ t + 1 by omega)]
  have hP : ∀ t, RowNonnegative (P t) := by
    intro t
    induction t with
    | zero => rw [hbase]; exact hM
    | succ t ih =>
      rw [hs]
      exact rowNonnegative_add_previous ih (t + 1) t (by intro x hx; omega)
        (by omega) (hc (t + 1) (by omega))
  intro I hI
  let b := univ.sup I
  have hi : ∀ i, I i ≤ b := fun i => le_sup (mem_univ i)
  have he : (P b).submatrix I id = N.submatrix I id := by
    ext i j
    change (if I i ≤ b then N (I i) else M (I i)) j = N (I i) j
    rw [ite_eq_left (hi i)]
  rw [← he]
  exact hP b I hI

/-- All ordered minors of a positive inverse product are nonnegative. -/
theorem inverseEntries_ordered_minors (p : ℕ) (a : Entries)
    (ha : ∀ j < p, ∀ n, 0 < n → 0 ≤ a j n) {k : ℕ}
    (J : Fin k → ℕ) (hJ : StrictMono J) :
    RowNonnegative (fun n j => inverseEntries a p n (J j)) := by
  induction p generalizing a with
  | zero =>
    intro I hI
    exact identity_ordered_minor I J hI hJ
  | succ p ih =>
    apply rowNonnegative_forward
      (fun n j => inverseEntries (fun i t => a (i + 1) t) p n (J j))
      (fun n j => inverseEntries a (p + 1) n (J j)) (a 0)
    · exact ih _ (fun i hi n hn => ha (i + 1) (by omega) n hn)
    · exact ha 0 (by omega)
    · funext j; simp
    · intro n; funext j
      exact inverseEntries_succ a p n (J j)

#print axioms inverseEntries_ordered_minors
end BTP.SemiInfinite
