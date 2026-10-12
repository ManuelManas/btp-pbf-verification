import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic

/-!
# Lemma 2.4: finite row-by-row refactorization

Formalization date: 2026-10-08. Version: v01.

Source: BTP_PBF_Normal_2026-10-07_v16.tex, label `lem:rowwise`.
The factors are numbered from the right, starting at zero. Thus `a j n`
is the manuscript's `a_{p-j}(n)`. The initial zero pattern is `n ≤ j`.
-/

open scoped BigOperators Topology Matrix.Norms.Elementwise
open Filter Finset Matrix

noncomputable section

namespace BTP

/-- Subdiagonal entries, indexed by factor (from the right) and row. -/
abbrev Entries := ℕ → ℕ → ℝ

/-- Entry at displacement `r` of the product of the `p` rightmost factors.
The recurrence is precisely multiplication by a unit lower bidiagonal matrix. -/
def entry (a : Entries) : ℕ → ℕ → ℕ → ℝ
  | 0, _, r => if r = 0 then 1 else 0
  | _p + 1, _, 0 => 1
  | p + 1, n, r + 1 => entry a p n (r + 1) + a p n * entry a p (n - 1) r

@[simp] theorem entry_zero (a : Entries) (p n : ℕ) : entry a p n 0 = 1 := by
  cases p <;> simp [entry]

/-- Bandwidth: `p` factors cannot decrease the index more than `p` times. -/
theorem entry_band (a : Entries) (p n r : ℕ) (h : p < r) : entry a p n r = 0 := by
  induction p generalizing n r with
  | zero => simp [entry, Nat.ne_of_gt h]
  | succ p ih =>
    cases r with
    | zero => omega
    | succ r => simp [entry, ih n (r + 1) (by omega), ih (n - 1) r (by omega)]

/-- Grouping product paths by their first selected factor gives the row system. -/
theorem entry_row (a : Entries) (p n r : ℕ) :
    entry a p n (r + 1) = ∑ j ∈ range p, a j n * entry a j (n - 1) r := by
  induction p with
  | zero => simp [entry]
  | succ p ih => simp [entry, sum_range_succ, ih]

/-- On the extreme diagonal every factor must supply its subdiagonal entry. -/
theorem entry_diag_step (a : Entries) (p n : ℕ) :
    entry a (p + 1) n (p + 1) = a p n * entry a p (n - 1) p := by
  simp [entry, entry_band a p n (p + 1) (by omega)]

/-- Positivity of the pivot under the Metelmann initial pattern. -/
theorem entry_diag_pos (a : Entries) (p n : ℕ) (hpn : p ≤ n)
    (ha : ∀ j < p, ∀ m ≤ n, j < m → 0 < a j m) : 0 < entry a p n p := by
  induction p generalizing n with
  | zero => simp [entry]
  | succ p ih =>
    rw [entry_diag_step]
    apply mul_pos (ha p (by omega) n le_rfl (by omega))
    exact ih (n - 1) (by omega) (fun j hj m hm hjm => ha j (by omega) m (by omega) hjm)

/-- Entries in a row only involve that row and preceding rows. -/
theorem entry_congr (a b : Entries) (p n r : ℕ)
    (h : ∀ j < p, ∀ m ≤ n, a j m = b j m) : entry a p n r = entry b p n r := by
  induction p generalizing n r with
  | zero => rfl
  | succ p ih =>
    cases r with
    | zero => rfl
    | succ r =>
      simp only [entry]
      rw [ih n (r + 1) (fun j hj m hm => h j (by omega) m hm), h p (by omega) n le_rfl,
        ih (n - 1) r (fun j hj m hm => h j (by omega) m (by omega))]

/-- Each product coefficient is analytic whenever its subdiagonal data are. -/
theorem entry_analytic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : E → Entries) (z : E) (ha : ∀ j n, AnalyticAt ℝ (fun u => a u j n) z)
    (p n r : ℕ) : AnalyticAt ℝ (fun u => entry (a u) p n r) z := by
  induction p generalizing n r with
  | zero => exact analyticAt_const
  | succ p ih =>
    cases r with
    | zero => exact analyticAt_const
    | succ r => exact (ih n (r + 1)).add ((ha p n).mul (ih (n - 1) r))

/-- The coefficient matrix in a single row, with factors numbered from the right. -/
def rowMatrix (a : Entries) (k n : ℕ) : Matrix (Fin k) (Fin k) ℝ :=
  fun r j => entry a j (n - 1) r

theorem rowMatrix_upper (a : Entries) (k n : ℕ) :
    (rowMatrix a k n).IsUpperTriangular := by
  intro r j h
  exact entry_band a j (n - 1) r h

theorem rowMatrix_det_pos (a : Entries) (k n : ℕ) (hkn : k ≤ n)
    (ha : ∀ j < k, ∀ m < n, j < m → 0 < a j m) :
    0 < (rowMatrix a k n).det := by
  rw [Matrix.det_of_isUpperTriangular (rowMatrix_upper a k n)]
  apply Finset.prod_pos
  intro j _
  apply entry_diag_pos a j (n - 1) (by omega)
  intro i hi m hm him
  exact ha i (by omega) m (by omega) him

/-- The determinant is a polynomial in the entries, hence analytic. -/
theorem det_analytic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : ℕ} (C : E → Matrix (Fin k) (Fin k) ℝ) (z : E)
    (hC : ∀ i j, AnalyticAt ℝ (fun u => C u i j) z) :
    AnalyticAt ℝ (fun u => (C u).det) z := by
  simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  apply Finset.analyticAt_fun_sum
  intro σ _
  apply AnalyticAt.mul analyticAt_const
  exact Finset.analyticAt_fun_prod _ (fun i _ => hC (σ i) i)

/-- Cramer's formula is used only to express the unique row solution by
rational operations. It is the same solution as back substitution. -/
def solve {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) (y : Fin k → ℝ) : Fin k → ℝ :=
  C.det⁻¹ • C.cramer y

theorem solve_correct {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) (y : Fin k → ℝ)
    (hC : C.det ≠ 0) : C *ᵥ solve C y = y := by
  simp [solve, Matrix.mulVec_smul, smul_smul, hC]

theorem solve_unique {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) (y x : Fin k → ℝ)
    (hC : C.det ≠ 0) (hx : C *ᵥ x = y) : solve C y = x := by
  apply (Matrix.mulVec_injective_iff_isUnit.mpr ?_)
  · exact (solve_correct C y hC).trans hx.symm
  · exact (Matrix.isUnit_iff_isUnit_det C).mpr (isUnit_iff_ne_zero.mpr hC)

theorem solve_analytic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : ℕ} (C : E → Matrix (Fin k) (Fin k) ℝ) (y : E → Fin k → ℝ) (z : E)
    (hC : ∀ i j, AnalyticAt ℝ (fun u => C u i j) z)
    (hy : ∀ i, AnalyticAt ℝ (fun u => y u i) z) (hdet : (C z).det ≠ 0)
    (j : Fin k) : AnalyticAt ℝ (fun u => solve (C u) (y u) j) z := by
  simp only [solve, Pi.smul_apply, smul_eq_mul, Matrix.cramer_apply]
  apply ((det_analytic C z hC).inv hdet).mul
  apply det_analytic
  intro i l
  by_cases h : l = j
  · subst l
    simpa using hy i
  · simpa [Matrix.updateCol_ne h] using hC i l

/-- One coordinate for each initial zero: factor `j` has free rows `1,…,j`. -/
abbrev Free (p : ℕ) := (j : Fin p) × Fin j.val
abbrev Parameters (p : ℕ) := Free p → ℝ

theorem number_of_parameters (p : ℕ) : Fintype.card (Free p) = p * (p - 1) / 2 := by
  simp only [Free, Fintype.card_sigma, Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => i), Finset.sum_range_id]

/-- Read the parameter of a free position; all other positions give zero. -/
def freeValue (p : ℕ) (u : Parameters p) (j n : ℕ) : ℝ :=
  if h : j < p ∧ 0 < n ∧ n ≤ j then
    u ⟨⟨j, h.1⟩, ⟨n - 1, by change n - 1 < j; omega⟩⟩
  else 0

@[simp] theorem freeValue_zero (p j n : ℕ) : freeValue p 0 j n = 0 := by
  simp [freeValue]

theorem freeValue_analytic (p j n : ℕ) :
    AnalyticAt ℝ (fun u : Parameters p => freeValue p u j n) 0 := by
  unfold freeValue
  split_ifs with h
  · exact (show Parameters p →L[ℝ] ℝ from ContinuousLinearMap.proj _).analyticAt _
  · exact analyticAt_const

theorem freeValue_pos (p j n : ℕ) (hj : j < p) (hn : 0 < n) (hnj : n ≤ j)
    (u : Parameters p) (hu : ∀ c, 0 < u c) : 0 < freeValue p u j n := by
  unfold freeValue
  split_ifs with h
  · exact hu _
  · exact (h ⟨hj, hn, hnj⟩).elim

/-- Invariant after rows `1,…,m` have been constructed. -/
structure RowState (p : ℕ) (a₀ : Entries) (m : ℕ) (A : Parameters p → Entries) : Prop where
  analytic : ∀ j n, AnalyticAt ℝ (fun u => A u j n) 0
  initial : A 0 = a₀
  free : ∀ j < p, ∀ n, 0 < n → n ≤ m → n ≤ j →
    ∀ u, A u j n = freeValue p u j n
  product : ∀ n ≤ m, ∀ r ≤ n,
    ∀ᶠ u in 𝓝 (0 : Parameters p), entry (A u) p n r = entry a₀ p n r

theorem initial_state (p : ℕ) (a₀ : Entries) : RowState p a₀ 0 (fun _ => a₀) where
  analytic _ _ := analyticAt_const
  initial := rfl
  free := by intros; omega
  product := by intros; exact Eventually.of_forall (fun _ => rfl)

/-- Sum of the terms with freely chosen coefficients in row `n`. -/
def freeSum (p k n r : ℕ) (A : Parameters p → Entries) (u : Parameters p) : ℝ :=
  ∑ j ∈ Ico k p, freeValue p u j n * entry (A u) j (n - 1) r

/-- Right-hand side of the square row system. -/
def rowRhs (p k n : ℕ) (a₀ : Entries) (A : Parameters p → Entries)
    (u : Parameters p) (r : Fin k) : ℝ :=
  entry a₀ p n (r.val + 1) - freeSum p k n r A u

/-- Change only the current row; solve the nonfree positions. -/
def nextRow (p n : ℕ) (a₀ : Entries) (A : Parameters p → Entries)
    (u : Parameters p) (j m : ℕ) : ℝ :=
  if j < p ∧ m = n then
    if h : j < min p n then
      solve (rowMatrix (A u) (min p n) n) (rowRhs p (min p n) n a₀ A u) ⟨j, h⟩
    else freeValue p u j n
  else A u j m

/-- Rows that have already been constructed are unaffected. -/
theorem nextRow_old (p n : ℕ) (a₀ : Entries) (A : Parameters p → Entries)
    (u : Parameters p) (j m : ℕ) (hm : m < n) : nextRow p n a₀ A u j m = A u j m := by
  simp [nextRow, Nat.ne_of_lt hm]

/-- The initial row system is solved by the prescribed initial factorization. -/
theorem initial_row_system (p n : ℕ) (a₀ : Entries) (_hn : 0 < n)
    (hz : ∀ j < p, n ≤ j → a₀ j n = 0) :
    rowMatrix a₀ (min p n) n *ᵥ (fun j => a₀ j n) =
      fun r => entry a₀ p n (r.val + 1) := by
  ext r
  simp only [Matrix.mulVec, dotProduct, rowMatrix]
  rw [entry_row, ← Finset.sum_range_add_sum_Ico _ (min_le_left p n)]
  have ht : ∑ j ∈ Ico (min p n) p, a₀ j n * entry a₀ j (n - 1) r = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    obtain ⟨hkj, hjp⟩ := mem_Ico.mp hj
    have hnj : n ≤ j := by omega
    simp [hz j hjp hnj]
  rw [ht, add_zero, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

/-- The inductive step, including analyticity, agreement at zero, the free
coordinates, and exact equality of all product rows already constructed. -/
theorem state_step (p n : ℕ) (a₀ : Entries) (A : Parameters p → Entries)
    (hn : 0 < n) (hA : RowState p a₀ (n - 1) A)
    (hz : ∀ j < p, n ≤ j → a₀ j n = 0)
    (hp : ∀ j < min p n, ∀ m < n, j < m → 0 < a₀ j m) :
    RowState p a₀ n (nextRow p n a₀ A) := by
  let k := min p n
  let C := fun u => rowMatrix (A u) k n
  let y := rowRhs p k n a₀ A
  have hc : ∀ r j, AnalyticAt ℝ (fun u => C u r j) 0 := by
    intro r j
    exact entry_analytic A 0 hA.analytic j (n - 1) r
  have hy : ∀ r, AnalyticAt ℝ (fun u => y u r) 0 := by
    intro r
    apply AnalyticAt.sub analyticAt_const
    apply Finset.analyticAt_fun_sum
    intro j _
    exact (freeValue_analytic p j n).mul (entry_analytic A 0 hA.analytic j (n - 1) r)
  have hd : (C 0).det ≠ 0 := by
    dsimp [C]
    rw [hA.initial]
    exact ne_of_gt (rowMatrix_det_pos a₀ k n (min_le_right p n) hp)
  have hx : solve (C 0) (y 0) = fun j : Fin k => a₀ j n := by
    apply solve_unique _ _ _ hd
    have hy0 : y 0 = fun r => entry a₀ p n (r.val + 1) := by
      funext r
      simp [y, rowRhs, freeSum]
    rw [hy0]
    simpa [C, k, hA.initial] using initial_row_system p n a₀ hn hz
  have ha : ∀ j m, AnalyticAt ℝ (fun u => nextRow p n a₀ A u j m) 0 := by
    intro j m
    unfold nextRow
    split_ifs with h hk
    · exact solve_analytic C y 0 hc hy hd ⟨j, hk⟩
    · exact freeValue_analytic p j n
    · exact hA.analytic j m
  refine ⟨ha, ?_, ?_, ?_⟩
  · funext j m
    unfold nextRow
    split_ifs with h hk
    · obtain ⟨hjp, rfl⟩ := h
      exact congrFun hx ⟨j, hk⟩
    · obtain ⟨hjp, rfl⟩ := h
      rw [freeValue_zero, hz j hjp (by omega)]
    · exact congrFun (congrFun hA.initial j) m
  · intro j hj m hm hmn hmj u
    by_cases h : m = n
    · subst m
      have hk : ¬j < min p n := by omega
      simp [nextRow, hj, hk]
    · rw [nextRow_old p n a₀ A u j m (by omega)]
      exact hA.free j hj m hm (by omega) hmj u
  · intro m hmn r hr
    by_cases h : m < n
    · filter_upwards [hA.product m (by omega) r hr] with u hu
      rw [entry_congr (nextRow p n a₀ A u) (A u) p m r ?_, hu]
      intro j hj t ht
      exact nextRow_old p n a₀ A u j t (by omega)
    · have hmn' : m = n := by omega
      subst m
      cases r with
      | zero => exact Eventually.of_forall (fun _ => by simp)
      | succ r =>
        by_cases hrp : p < r + 1
        · exact Eventually.of_forall (fun u => by rw [entry_band _ _ _ _ hrp, entry_band _ _ _ _ hrp])
        · have hrk : r < k := by dsimp [k]; omega
          filter_upwards [(det_analytic C 0 hc).continuousAt.eventually_ne hd] with u hu
          have hcoeff : ∀ j, entry (nextRow p n a₀ A u) j (n - 1) r = entry (A u) j (n - 1) r := by
            intro j
            apply entry_congr
            intro i hi t ht
            exact nextRow_old p n a₀ A u i t (by omega)
          have hs := congrFun (solve_correct (C u) (y u) hu) ⟨r, hrk⟩
          have hsolve : ∑ j ∈ range k, nextRow p n a₀ A u j n *
              entry (nextRow p n a₀ A u) j (n - 1) r = y u ⟨r, hrk⟩ := by
            rw [← Fin.sum_univ_eq_sum_range]
            calc
              _ = ∑ j : Fin k, C u ⟨r, hrk⟩ j * solve (C u) (y u) j := by
                apply Finset.sum_congr rfl
                intro j _
                have hjp : j.val < p := lt_of_lt_of_le j.isLt (min_le_left p n)
                simp only [hcoeff, nextRow, hjp, and_self, ite_true, j.isLt, dite_eq_left,
                  C, rowMatrix, k, y]
                exact mul_comm _ _
              _ = _ := hs
          have hfree : ∑ j ∈ Ico k p, nextRow p n a₀ A u j n *
              entry (nextRow p n a₀ A u) j (n - 1) r = freeSum p k n r A u := by
            apply Finset.sum_congr rfl
            intro j hj
            obtain ⟨hkj, hjp⟩ := mem_Ico.mp hj
            have hjk : ¬j < min p n := by omega
            simp [nextRow, hjp, hjk, hcoeff]
          rw [entry_row, ← Finset.sum_range_add_sum_Ico _ (min_le_left p n), hsolve, hfree]
          simp [y, rowRhs]

/-- The construction terminates after finitely many rows. -/
theorem construct_rows (p d : ℕ) (a₀ : Entries) (hpd : p < d)
    (hz : ∀ j < p, ∀ n, 0 < n → n ≤ j → a₀ j n = 0)
    (hp : ∀ j < p, ∀ n < d, j < n → 0 < a₀ j n) :
    ∃ A : Parameters p → Entries, RowState p a₀ (d - 1) A := by
  have h : ∀ m < d, ∃ A : Parameters p → Entries, RowState p a₀ m A := by
    intro m
    induction m with
    | zero => intro _; exact ⟨fun _ => a₀, initial_state p a₀⟩
    | succ m ih =>
      intro hm
      obtain ⟨A, hA⟩ := ih (by omega)
      refine ⟨nextRow p (m + 1) a₀ A, state_step p (m + 1) a₀ A (by omega) ?_ ?_ ?_⟩
      · simpa using hA
      · intro j hj hnj
        exact hz j hj (m + 1) (by omega) hnj
      · intro j hj t ht hjt
        exact hp j (lt_of_lt_of_le hj (min_le_left _ _)) t (by omega) hjt
  exact h (d - 1) (by omega)

/-- The actual finite unit lower bidiagonal matrix. -/
def bidiagonal (d : ℕ) (a : ℕ → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  (1 : Matrix (Fin d) (Fin d) ℝ) +
    Matrix.of (fun i j : Fin d => if i.val = j.val + 1 then a i.val else 0)

/-- Product in the order of the manuscript, despite numbering from the right. -/
def lowerProduct (d : ℕ) (a : Entries) : ℕ → Matrix (Fin d) (Fin d) ℝ
  | 0 => 1
  | p + 1 => bidiagonal d (a p) * lowerProduct d a p

/-- Multiplication by a bidiagonal matrix uses only the current and preceding row. -/
theorem bidiagonal_mul_pos {d : ℕ} (a : ℕ → ℝ) (M : Matrix (Fin d) (Fin d) ℝ)
    (i j : Fin d) (hi : 0 < i.val) :
    (bidiagonal d a * M) i j = M i j + a i.val * M ⟨i.val - 1, by omega⟩ j := by
  rw [bidiagonal, Matrix.add_mul, Matrix.one_mul]
  simp only [Matrix.add_apply, Matrix.mul_apply]
  congr 1
  rw [Finset.sum_eq_single (⟨i.val - 1, by omega⟩ : Fin d)]
  · simp only [Matrix.of_apply, ite_eq_left (show i.val = i.val - 1 + 1 by omega)]
  · intro k _ hk
    have hne : i.val ≠ k.val + 1 := by
      intro h
      apply hk
      apply Fin.ext
      change k.val = i.val - 1
      omega
    simp [hne]
  · simp

theorem bidiagonal_mul_zero {d : ℕ} (a : ℕ → ℝ) (M : Matrix (Fin d) (Fin d) ℝ)
    (i j : Fin d) (hi : i.val = 0) : (bidiagonal d a * M) i j = M i j := by
  rw [bidiagonal, Matrix.add_mul, Matrix.one_mul]
  simp [Matrix.add_apply, Matrix.mul_apply, hi]

/-- The recursively defined coefficients are exactly the entries of the matrix product. -/
theorem lowerProduct_entry {d : ℕ} (a : Entries) (p : ℕ) (i j : Fin d) :
    lowerProduct d a p i j = if j.val ≤ i.val then entry a p i.val (i.val - j.val) else 0 := by
  induction p generalizing i j with
  | zero =>
    simp only [lowerProduct, Matrix.one_apply, entry]
    by_cases hij : i = j
    · subst j; simp
    · have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
      by_cases h : j.val ≤ i.val
      · simp [hij, h, Nat.sub_ne_zero_of_lt (by omega : j.val < i.val)]
      · simp [hij, h]
  | succ p ih =>
    simp only [lowerProduct]
    by_cases hi : 0 < i.val
    · rw [bidiagonal_mul_pos _ _ _ _ hi, ih]
      have hp := ih (⟨i.val - 1, by omega⟩ : Fin d) j
      rw [hp]
      by_cases h : j.val ≤ i.val
      · by_cases heq : j.val = i.val
        · simp [heq, show ¬ i.val ≤ i.val - 1 by omega]
        · have hjprev : j.val ≤ i.val - 1 := by omega
          have hr : i.val - j.val = (i.val - 1 - j.val) + 1 := by omega
          simp [h, hjprev, hr, entry]
      · have hjprev : ¬ j.val ≤ i.val - 1 := by omega
        simp [h, hjprev]
    · have hi0 : i.val = 0 := by omega
      rw [bidiagonal_mul_zero _ _ _ _ hi0, ih]
      by_cases h : j.val ≤ i.val
      · have hj : j.val = 0 := by omega
        simp [hi0, hj]
      · simp [h]

/-- All finitely many product entries agree on one neighborhood. -/
theorem RowState.eventually_product {p d : ℕ} {a₀ : Entries} {A : Parameters p → Entries}
    (hA : RowState p a₀ (d - 1) A) :
    ∀ᶠ u in 𝓝 (0 : Parameters p), lowerProduct d (A u) p = lowerProduct d a₀ p := by
  have he : ∀ i j : Fin d, ∀ᶠ u in 𝓝 (0 : Parameters p),
      lowerProduct d (A u) p i j = lowerProduct d a₀ p i j := by
    intro i j
    by_cases h : j.val ≤ i.val
    · filter_upwards [hA.product i.val (by omega) (i.val - j.val) (by omega)] with u hu
      simpa [lowerProduct_entry, h] using hu
    · exact Eventually.of_forall (fun u => by simp [lowerProduct_entry, h])
  filter_upwards [eventually_all.mpr (fun i => eventually_all.mpr (he i))] with u hu
  exact Matrix.ext fun i j => hu i j

/-- Originally positive entries remain positive on one neighborhood. -/
theorem RowState.eventually_positive {p d : ℕ} {a₀ : Entries} {A : Parameters p → Entries}
    (hA : RowState p a₀ (d - 1) A)
    (hp : ∀ j < p, ∀ n < d, j < n → 0 < a₀ j n) :
    ∀ᶠ u in 𝓝 (0 : Parameters p), ∀ j : Fin p, ∀ n : Fin d,
      j.val < n.val → 0 < A u j.val n.val := by
  apply eventually_all.mpr
  intro j
  apply eventually_all.mpr
  intro n
  by_cases h : j.val < n.val
  · have h0 : 0 < A 0 j.val n.val := by rw [hA.initial]; exact hp j j.isLt n n.isLt h
    filter_upwards [tendsto_const_nhds.eventually_lt (hA.analytic j n).continuousAt h0] with u hu
    exact fun _ => hu
  · exact Eventually.of_forall (fun _ hu => (h hu).elim)

/-- A neighborhood on which every relevant entry is analytic. -/
theorem RowState.eventually_analytic {p d : ℕ} {a₀ : Entries} {A : Parameters p → Entries}
    (hA : RowState p a₀ (d - 1) A) :
    ∀ᶠ u in 𝓝 (0 : Parameters p), ∀ j : Fin p, ∀ n : Fin d,
      AnalyticAt ℝ (fun v => A v j.val n.val) u := by
  exact eventually_all.mpr (fun j => eventually_all.mpr (fun n =>
    (hA.analytic j n).eventually_analyticAt))

/-- Lemma 2.4 in subdiagonal coordinates, with an explicit common positive radius. -/
theorem refactorization_entries (p d : ℕ) (a₀ : Entries) (hpd : p < d)
    (hz : ∀ j < p, ∀ n, 0 < n → n ≤ j → a₀ j n = 0)
    (hp : ∀ j < p, ∀ n < d, j < n → 0 < a₀ j n) :
    ∃ A : Parameters p → Entries, ∃ ε : ℝ, 0 < ε ∧ A 0 = a₀ ∧
      (∀ j < p, ∀ n, 0 < n → n ≤ j → ∀ u, A u j n = freeValue p u j n) ∧
      (∀ u, ‖u‖ < ε →
        (∀ j : Fin p, ∀ n : Fin d, AnalyticAt ℝ (fun v => A v j n) u) ∧
        lowerProduct d (A u) p = lowerProduct d a₀ p ∧
        ((∀ c, 0 < u c) → ∀ j < p, ∀ n < d, 0 < n → 0 < A u j n)) := by
  obtain ⟨A, hA⟩ := construct_rows p d a₀ hpd hz hp
  have hall := hA.eventually_analytic.and (hA.eventually_product.and (hA.eventually_positive hp))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hall
  refine ⟨A, ε, hε, hA.initial, ?_, ?_⟩
  · intro j hj n hn hnj u
    exact hA.free j hj n hn (by omega) hnj u
  · intro u hu
    obtain ⟨ha, heq, hpos⟩ := hball (by simpa using hu)
    refine ⟨ha, heq, ?_⟩
    intro hfree j hj n hnd hn
    by_cases hnj : n ≤ j
    · rw [hA.free j hj n hn (by omega) hnj]
      exact freeValue_pos p j n hj hn hnj u hfree
    · apply hpos ⟨j, hj⟩ ⟨n, hnd⟩
      change j < n
      omega

/-- Diagonal entries are one and the only possible off-diagonal entries are
on the first lower diagonal. -/
def UnitLowerBidiagonal {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  (∀ i, M i i = 1) ∧ ∀ i j, i ≠ j → i.val ≠ j.val + 1 → M i j = 0

def PositiveLowerBidiagonal {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  UnitLowerBidiagonal M ∧ ∀ i j, i.val = j.val + 1 → 0 < M i j

theorem bidiagonal_unit (d : ℕ) (a : ℕ → ℝ) : UnitLowerBidiagonal (bidiagonal d a) := by
  constructor
  · intro i
    simp [bidiagonal, Matrix.add_apply]
  · intro i j hne hsub
    simp [bidiagonal, Matrix.add_apply, hne, hsub]

theorem bidiagonal_subdiagonal {d : ℕ} (a : ℕ → ℝ) (i j : Fin d)
    (h : i.val = j.val + 1) : bidiagonal d a i j = a i.val := by
  have hne : i ≠ j := by intro heq; subst j; omega
  simp [bidiagonal, Matrix.add_apply, hne, h]

theorem bidiagonal_analytic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {d : ℕ} (a : E → ℕ → ℝ) (u : E)
    (ha : ∀ n : Fin d, AnalyticAt ℝ (fun v => a v n) u) :
    AnalyticAt ℝ (fun v => bidiagonal d (a v)) u := by
  apply AnalyticAt.pi
  intro i
  apply AnalyticAt.pi
  intro j
  simp only [bidiagonal, Matrix.add_apply, Matrix.of_apply]
  by_cases h : i.val = j.val + 1
  · simp only [h, ite_true]
    exact AnalyticAt.add analyticAt_const (by simpa only [h] using ha i)
  · simp only [h, ite_false, add_zero]
    exact analyticAt_const

/-- Explicit list product; the largest index is the leftmost factor. -/
theorem lowerProduct_list (d : ℕ) (a : Entries) (p : ℕ) :
    lowerProduct d a p = ((List.range p).reverse.map (fun j => bidiagonal d (a j))).prod := by
  induction p with
  | zero => simp [lowerProduct]
  | succ p ih => simp [lowerProduct, List.range_succ, List.reverse_append, ih]

/-- **Lemma 2.4.** Arbitrary finite dimension and bandwidth. Each initial zero
is an independent parameter, the factorization is preserved exactly, the
families are analytic on a common ball, and all factors are positive when
all parameters are positive in that ball.

Index translation: formal factor `j` is manuscript factor `p-j`.
The product below therefore runs through `p-1,…,0`. The type `Free p`
has exactly `p*(p-1)/2` elements (`number_of_parameters`). -/
theorem lemma_2_4 (p d : ℕ) (a₀ : Entries) (hpd : p < d)
    (hz : ∀ j < p, ∀ n, 0 < n → n ≤ j → a₀ j n = 0)
    (hp : ∀ j < p, ∀ n < d, j < n → 0 < a₀ j n) :
    ∃ L : Parameters p → ℕ → Matrix (Fin d) (Fin d) ℝ, ∃ ε : ℝ,
      0 < ε ∧
      (∀ j, L 0 j = bidiagonal d (a₀ j)) ∧
      (∀ u j, UnitLowerBidiagonal (L u j)) ∧
      (∀ c : Free p, ∀ u,
        L u c.1.val ⟨c.2.val + 1, by have := c.2.isLt; have := c.1.isLt; omega⟩
          ⟨c.2.val, by have := c.2.isLt; have := c.1.isLt; omega⟩ = u c) ∧
      (∀ u, ‖u‖ < ε →
        (∀ j < p, AnalyticAt ℝ (fun v => L v j) u) ∧
        ((List.range p).reverse.map (L u)).prod = lowerProduct d a₀ p ∧
        ((∀ c, 0 < u c) → ∀ j < p, PositiveLowerBidiagonal (L u j))) := by
  obtain ⟨A, ε, hε, hinit, hfree, hball⟩ := refactorization_entries p d a₀ hpd hz hp
  let L := fun u j => bidiagonal d (A u j)
  refine ⟨L, ε, hε, ?_, ?_, ?_, ?_⟩
  · intro j
    simp [L, hinit]
  · intro u j
    exact bidiagonal_unit d (A u j)
  · intro c u
    dsimp only [L]
    rw [bidiagonal_subdiagonal _ _ _ rfl]
    have hnj : c.2.val + 1 ≤ c.1.val := by have := c.2.isLt; omega
    rw [hfree c.1.val c.1.isLt (c.2.val + 1) (by omega) hnj]
    simp [freeValue, c.1.isLt, hnj]
  · intro u hu
    obtain ⟨ha, heq, hpos⟩ := hball u hu
    refine ⟨?_, ?_, ?_⟩
    · intro j hj
      exact bidiagonal_analytic (fun v => A v j) u (ha ⟨j, hj⟩)
    · exact (lowerProduct_list d (A u) p).symm.trans heq
    · intro hu j hj
      refine ⟨bidiagonal_unit d (A u j), ?_⟩
      intro i l hil
      dsimp only [L]
      rw [bidiagonal_subdiagonal _ _ _ hil]
      exact hpos hu j hj i.val i.isLt (by omega)

#print axioms lemma_2_4
#print axioms number_of_parameters

end BTP
