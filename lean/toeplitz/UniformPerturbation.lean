import ExtractionPositive

/-! # A single neighborhood controls infinitely many rows -/
open Matrix Finset Filter
open scoped Topology
noncomputable section
namespace BTP.SemiInfinite

/-- Multilinearity in the columns. Repeated selections contribute zero. -/
theorem det_rectangular_mul {k p : ℕ} (A : Matrix (Fin k) (Fin p) ℝ)
    (C : Matrix (Fin p) (Fin k) ℝ) :
    (A * C).det = ∑ c : Fin k → Fin p,
      (∏ j, C (c j) j) * (Matrix.of fun i j : Fin k => A i (c j)).det := by
  let f : MultilinearMap ℝ (fun _ : Fin k => Fin k → ℝ) ℝ :=
    Matrix.detRowAlternating.toMultilinearMap
  let g := fun j : Fin k => fun h : Fin p => fun i : Fin k => C h j * A i h
  have he := f.map_sum g
  have hleft : f (fun j => ∑ h, g j h) = (A * C).det := by
    change (Matrix.of fun j i => (∑ h, g j h) i).det = (A * C).det
    rw [← Matrix.det_transpose (A * C)]
    congr 1
    ext j i
    simp only [Matrix.of_apply, Finset.sum_apply, Matrix.transpose_apply, Matrix.mul_apply, g]
    apply sum_congr rfl
    intro h _
    ring
  rw [hleft] at he
  rw [he]
  apply sum_congr rfl
  intro c _
  have hc := f.map_smul_univ (fun j => C (c j) j) (fun j i => A i (c j))
  change f (fun j => C (c j) j • (fun i => A i (c j))) = _
  rw [hc]
  change (∏ j, C (c j) j) * (Matrix.of fun j i : Fin k => A i (c j)).det = _
  rw [← Matrix.det_transpose (Matrix.of fun i j : Fin k => A i (c j))]
  rfl

/-- A finite sum of coefficient errors controls every row simultaneously. -/
theorem uniform_determinant_positivity {E : Type*} [NormedAddCommGroup E]
    {k p : ℕ} (A : ℕ → Matrix (Fin k) (Fin p) ℝ) (δ : ℕ → ℝ)
    (C : E → Matrix (Fin p) (Fin k) ℝ)
    (hδ : ∀ n, 0 < δ n)
    (hzero : ∀ n, (A n * C 0).det = δ n)
    (hC : ∀ i j, ContinuousAt (fun u => C u i j) 0)
    {M : ℝ} (hbound : ∀ n, ∀ c : Fin k → Fin p,
      |(Matrix.of fun i j : Fin k => A n i (c j)).det / δ n| ≤ M) :
    ∀ᶠ u in 𝓝 (0 : E), ∀ n, 0 < (A n * C u).det := by
  let γ := fun u : E => fun c : Fin k → Fin p => ∏ j, C u (c j) j
  let ε := fun u : E => ∑ c : Fin k → Fin p, |γ u c - γ 0 c|
  have hγ : ∀ c, ContinuousAt (fun u => γ u c) 0 := by
    intro c
    dsimp [γ]
    fun_prop
  have hε : ContinuousAt ε 0 := by
    dsimp [ε]
    fun_prop
  have he0 : ε 0 = 0 := by simp [ε]
  have hsmall : ∀ᶠ u in 𝓝 (0 : E), M * ε u < (1 / 2 : ℝ) := by
    apply (continuousAt_const.mul hε).eventually_lt continuousAt_const
    change M * ε 0 < (1 / 2 : ℝ)
    rw [he0, mul_zero]
    norm_num
  filter_upwards [hsmall] with u hu
  intro n
  have hdiff : (A n * C u).det / δ n - 1 =
      ∑ c : Fin k → Fin p,
        ((Matrix.of fun i j : Fin k => A n i (c j)).det / δ n) * (γ u c - γ 0 c) := by
    rw [← div_self (hδ n).ne', ← hzero n, ← sub_div,
      det_rectangular_mul, det_rectangular_mul, ← sum_sub_distrib, sum_div]
    apply sum_congr rfl
    intro c _
    dsimp [γ]
    ring
  have herr : |(A n * C u).det / δ n - 1| ≤ M * ε u := by
    rw [hdiff]
    calc
      _ ≤ ∑ c : Fin k → Fin p,
          |((Matrix.of fun i j : Fin k => A n i (c j)).det / δ n) * (γ u c - γ 0 c)| :=
        abs_sum_le_sum_abs _ _
      _ ≤ ∑ c : Fin k → Fin p, M * |γ u c - γ 0 c| := by
        apply sum_le_sum
        intro c _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hbound n c) (abs_nonneg _)
      _ = M * ε u := by rw [mul_sum]
  have he := (abs_lt.mp (lt_of_le_of_lt herr hu)).1
  have hdpos : 0 < (A n * C u).det / δ n := by linarith
  exact (div_pos_iff_of_pos_right (hδ n)).mp hdpos

#print axioms uniform_determinant_positivity
end BTP.SemiInfinite
