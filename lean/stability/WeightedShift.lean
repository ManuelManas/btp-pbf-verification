import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Tactic

/-!
# Positive first-order recurrences and uniform geometric decay

The manuscript label is `stab:lem:weighted-shift`. Rows start at zero;
`w (n+1)` is the weight connecting rows `n` and `n+1`.
`w 0` is immaterial. The results assume only nonnegative weights,
which includes the strictly positive weights of the manuscript.
-/

open Finset
open scoped BigOperators
noncomputable section
namespace BTP.Stability

/-- The product of `N` weights following row `s`. -/
def blockProduct (w : ℕ → ℝ) (s N : ℕ) : ℝ :=
  ∏ i ∈ range N, w (s + i + 1)

@[simp] theorem blockProduct_zero (w : ℕ → ℝ) (s : ℕ) :
    blockProduct w s 0 = 1 := by simp [blockProduct]

theorem blockProduct_succ (w : ℕ → ℝ) (s N : ℕ) :
    blockProduct w s (N+1) = blockProduct w s N * w (s+N+1) := by
  simp [blockProduct, prod_range_succ]

theorem blockProduct_add (w : ℕ → ℝ) (s N K : ℕ) :
    blockProduct w s (N+K) = blockProduct w s N * blockProduct w (s+N) K := by
  simp only [blockProduct, prod_range_add]
  congr 1
  apply prod_congr rfl
  intro i _
  congr 1
  omega

theorem blockProduct_nonneg {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n) (s N : ℕ) :
    0 ≤ blockProduct w s N := by
  exact prod_nonneg fun i _ => hw _

/-- The sum of the nonnegative Green coefficients in row `n`. -/
def rowSum (w : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | n+1 => 1 + w (n+1) * rowSum w n

@[simp] theorem rowSum_zero (w : ℕ → ℝ) : rowSum w 0 = 1 := rfl

@[simp] theorem rowSum_succ (w : ℕ → ℝ) (n : ℕ) :
    rowSum w (n+1) = 1 + w (n+1) * rowSum w n := rfl

theorem rowSum_ge_one {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n) (n : ℕ) :
    1 ≤ rowSum w n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [rowSum_succ]
    have : 0 ≤ w (n+1) * rowSum w n := mul_nonneg (hw _) (by linarith)
    linarith

theorem rowSum_eq_sum (w : ℕ → ℝ) (n : ℕ) :
    rowSum w n = ∑ s ∈ range (n+1), blockProduct w s (n-s) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [rowSum_succ, ih, sum_range_succ (fun s => blockProduct w s (n+1-s)) (n+1)]
    simp only [Nat.sub_self, blockProduct_zero]
    rw [mul_sum]
    have hh : ∀ s ∈ range (n+1),
        w (n+1) * blockProduct w s (n-s) = blockProduct w s (n+1-s) := by
      intro s hs
      have hs' : s ≤ n := by simpa using hs
      have ha : n+1-s = (n-s)+1 := by omega
      rw [ha, blockProduct_succ]
      have hb : s+(n-s)+1 = n+1 := by omega
      rw [hb, mul_comm]
    rw [sum_congr rfl hh]
    ring

/-- An explicit scalar choice of contraction factor from a row-sum bound. -/
theorem geometric_of_rowSum_bound {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n)
    {M : ℝ} (hM : ∀ n, rowSum w n ≤ M) :
    ∃ C ρ : ℝ, 1 ≤ C ∧ 0 < ρ ∧ ρ < 1 ∧
      ∀ s N, blockProduct w s N ≤ C * ρ^N := by
  have hMone : 1 ≤ M := by simpa using hM 0
  let C : ℝ := M+1
  let ρ : ℝ := 1 - 1/C
  have hC : 1 < C := by dsimp [C]; linarith
  have hCpos : 0 < C := by linarith
  have hρpos : 0 < ρ := by
    dsimp [ρ]
    have : 1 / C < 1 := (div_lt_one hCpos).mpr hC
    linarith
  have hρlt : ρ < 1 := by
    dsimp [ρ]
    have : 0 < 1/C := one_div_pos.mpr hCpos
    linarith
  have hstep (n : ℕ) : w (n+1) * rowSum w n ≤ ρ * rowSum w (n+1) := by
    have hz : rowSum w (n+1) ≤ C := le_trans (hM _) (by dsimp [C]; linarith)
    have hzdiv : rowSum w (n+1)/C ≤ 1 := (div_le_one hCpos).mpr hz
    have he : ρ * rowSum w (n+1) = rowSum w (n+1) - rowSum w (n+1)/C := by
      dsimp [ρ]; ring
    rw [he]
    rw [rowSum_succ] at hzdiv ⊢
    linarith
  have hscaled (s N : ℕ) :
      blockProduct w s N * rowSum w s ≤ ρ^N * rowSum w (s+N) := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [blockProduct_succ, pow_succ]
      have h1 := mul_le_mul_of_nonneg_left ih (hw (s+N+1))
      have h2 := mul_le_mul_of_nonneg_left (hstep (s+N)) (pow_nonneg hρpos.le N)
      calc
        blockProduct w s N * w (s+N+1) * rowSum w s
            = w (s+N+1) * (blockProduct w s N * rowSum w s) := by ring
        _ ≤ w (s+N+1) * (ρ^N * rowSum w (s+N)) := h1
        _ = ρ^N * (w (s+N+1) * rowSum w (s+N)) := by ring
        _ ≤ ρ^N * (ρ * rowSum w (s+N+1)) := h2
        _ = ρ^N * ρ * rowSum w (s+(N+1)) := by simp only [Nat.add_assoc]; ring
  refine ⟨C, ρ, hC.le, hρpos, hρlt, ?_⟩
  intro s N
  calc
    blockProduct w s N ≤ blockProduct w s N * rowSum w s := by
      nlinarith [rowSum_ge_one hw s, blockProduct_nonneg hw s N]
    _ ≤ ρ^N * rowSum w (s+N) := hscaled s N
    _ ≤ ρ^N * C := mul_le_mul_of_nonneg_left
      (le_trans (hM _) (by dsimp [C]; linarith)) (pow_nonneg hρpos.le N)
    _ = C * ρ^N := mul_comm _ _

theorem geometric_partial_sum_le {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (n : ℕ) :
    ∑ j ∈ range n, ρ^j ≤ 1/(1-ρ) := by
  have hd : 0 < 1-ρ := by linarith
  apply (le_div_iff₀ hd).mpr
  have he := geom_sum_mul ρ n
  have hp : 0 ≤ ρ^n := pow_nonneg hρ0 n
  nlinarith

theorem rowSum_bound_of_geometric {w : ℕ → ℝ} {C ρ : ℝ}
    (hC : 0 ≤ C) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hg : ∀ s N, blockProduct w s N ≤ C * ρ^N) (n : ℕ) :
    rowSum w n ≤ C/(1-ρ) := by
  rw [rowSum_eq_sum]
  calc
    ∑ s ∈ range (n+1), blockProduct w s (n-s)
        ≤ ∑ s ∈ range (n+1), C * ρ^(n-s) := sum_le_sum fun s _ => hg s _
    _ = C * ∑ s ∈ range (n+1), ρ^(n-s) := (mul_sum ..).symm
    _ = C * ∑ s ∈ range (n+1), ρ^s := by
      congr 1
      simpa using sum_range_reflect (fun s => ρ^s) (n+1)
    _ ≤ C * (1/(1-ρ)) := mul_le_mul_of_nonneg_left (geometric_partial_sum_le hρ0 hρ1 _) hC
    _ = C/(1-ρ) := by ring

/-- The positive scalar equivalence used throughout Section 3, including
relative perturbations: no prior uniform upper bound on `w` is needed. -/
theorem rowSum_bounded_iff_geometric {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n) :
    (∃ M : ℝ, ∀ n, rowSum w n ≤ M) ↔
    (∃ C ρ : ℝ, 1 ≤ C ∧ 0 < ρ ∧ ρ < 1 ∧
      ∀ s N, blockProduct w s N ≤ C * ρ^N) := by
  constructor
  · rintro ⟨M, hM⟩
    exact geometric_of_rowSum_bound hw hM
  · rintro ⟨C, ρ, hC, hρ0, hρ1, hg⟩
    exact ⟨C/(1-ρ), rowSum_bound_of_geometric (by linarith) hρ0.le hρ1 hg⟩

/-- The forward solution with the first equation `v 0 = f 0`. -/
def forwardSolution (w f : ℕ → ℝ) : ℕ → ℝ
  | 0 => f 0
  | n+1 => f (n+1) + w (n+1) * forwardSolution w f n

@[simp] theorem forwardSolution_zero (w f : ℕ → ℝ) :
    forwardSolution w f 0 = f 0 := rfl

@[simp] theorem forwardSolution_succ (w f : ℕ → ℝ) (n : ℕ) :
    forwardSolution w f (n+1) = f (n+1) + w (n+1) * forwardSolution w f n := rfl

theorem forwardSolution_unique (w f v : ℕ → ℝ) (h0 : v 0 = f 0)
    (hs : ∀ n, v (n+1) - w (n+1) * v n = f (n+1)) :
    v = forwardSolution w f := by
  funext n
  induction n with
  | zero => exact h0
  | succ n ih => rw [forwardSolution_succ, ← ih]; linarith [hs n]

theorem forwardSolution_bound {w f : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n)
    {F : ℝ} (hF : ∀ n, |f n| ≤ F) (n : ℕ) :
    |forwardSolution w f n| ≤ F * rowSum w n := by
  induction n with
  | zero => simpa using hF 0
  | succ n ih =>
    rw [forwardSolution_succ, rowSum_succ]
    calc
      |f (n+1) + w (n+1) * forwardSolution w f n|
          ≤ |f (n+1)| + |w (n+1) * forwardSolution w f n| := abs_add_le _ _
      _ = |f (n+1)| + w (n+1) * |forwardSolution w f n| := by
        rw [abs_mul, abs_of_nonneg (hw _)]
      _ ≤ F + w (n+1) * (F * rowSum w n) :=
        add_le_add (hF _) (mul_le_mul_of_nonneg_left ih (hw _))
      _ = F * (1+w (n+1)*rowSum w n) := by ring

theorem forwardSolution_add (w f g : ℕ → ℝ) (n : ℕ) :
    forwardSolution w (f+g) n = forwardSolution w f n + forwardSolution w g n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [forwardSolution_succ, Pi.add_apply, ih]; ring

theorem forwardSolution_smul (w f : ℕ → ℝ) (c : ℝ) (n : ℕ) :
    forwardSolution w (c • f) n = c * forwardSolution w f n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [forwardSolution_succ, Pi.smul_apply, smul_eq_mul, ih]; ring

theorem forwardSolution_one (w : ℕ → ℝ) (n : ℕ) :
    forwardSolution w (fun _ => 1) n = rowSum w n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [forwardSolution_succ, rowSum_succ, ih]

/-- Bounded sequences on the discrete natural numbers, with their supremum norm.
This is the standard Banach space l-infinity, represented by mathlib's
bounded continuous functions on the discrete set of natural numbers. -/
abbrev BoundedSequence := BoundedContinuousFunction ℕ ℝ

/-- Turn a pointwise absolute bound into a bounded sequence. -/
def ofAbsBound (f : ℕ → ℝ) (M : ℝ) (h : ∀ n, |f n| ≤ M) : BoundedSequence :=
  BoundedContinuousFunction.mkOfDiscrete f (2*M) (by
    intro n m
    rw [Real.dist_eq]
    calc
      |f n-f m| ≤ |f n|+|f m| := abs_sub _ _
      _ ≤ M+M := add_le_add (h n) (h m)
      _ = 2*M := by ring)

@[simp] theorem ofAbsBound_apply (f : ℕ → ℝ) (M : ℝ) (h : ∀ n, |f n| ≤ M)
    (n : ℕ) : ofAbsBound f M h n = f n := rfl

theorem boundedSequence_abs_le (f : BoundedSequence) (n : ℕ) : |f n| ≤ ‖f‖ := by
  simpa only [Real.norm_eq_abs] using BoundedContinuousFunction.norm_coe_le_norm f n

/-- The bounded inverse defined by finite forward substitution in each row. -/
def solutionMap {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n) (M : ℝ)
    (hM : ∀ n, rowSum w n ≤ M) : BoundedSequence →L[ℝ] BoundedSequence :=
  let S : BoundedSequence →ₗ[ℝ] BoundedSequence :=
    { toFun := fun f => ofAbsBound (forwardSolution w f) (M*‖f‖) (by
        intro n
        calc
          |forwardSolution w f n| ≤ ‖f‖ * rowSum w n :=
            forwardSolution_bound hw (boundedSequence_abs_le f) n
          _ ≤ ‖f‖ * M := mul_le_mul_of_nonneg_left (hM n) (norm_nonneg f)
          _ = M*‖f‖ := mul_comm _ _)
      map_add' := by
        intro f g
        apply BoundedContinuousFunction.ext
        intro n
        exact forwardSolution_add w f g n
      map_smul' := by
        intro c f
        apply BoundedContinuousFunction.ext
        intro n
        exact forwardSolution_smul w f c n }
  S.mkContinuous M (by
    intro f
    apply BoundedContinuousFunction.norm_le_of_nonempty.mpr
    intro n
    change |forwardSolution w f n| ≤ M*‖f‖
    calc
      |forwardSolution w f n| ≤ ‖f‖ * rowSum w n :=
        forwardSolution_bound hw (boundedSequence_abs_le f) n
      _ ≤ ‖f‖ * M := mul_le_mul_of_nonneg_left (hM n) (norm_nonneg f)
      _ = M*‖f‖ := mul_comm _ _)

@[simp] theorem solutionMap_apply {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n) (M : ℝ)
    (hM : ∀ n, rowSum w n ≤ M) (f : BoundedSequence) (n : ℕ) :
    solutionMap hw M hM f n = forwardSolution w f n := rfl

/-- The first-order difference, including its initial equation. -/
def differenceFun (w f : ℕ → ℝ) : ℕ → ℝ
  | 0 => f 0
  | n+1 => f (n+1) - w (n+1) * f n

theorem differenceFun_bound (w f : BoundedSequence) (n : ℕ) :
    |differenceFun w f n| ≤ (1+‖w‖)*‖f‖ := by
  cases n with
  | zero =>
    change |f 0| ≤ _
    nlinarith [boundedSequence_abs_le f 0, norm_nonneg w, norm_nonneg f]
  | succ n =>
    change |f (n+1)-w (n+1)*f n| ≤ _
    calc
      |f (n+1)-w (n+1)*f n| ≤ |f (n+1)| + |w (n+1)*f n| := abs_sub _ _
      _ = |f (n+1)| + |w (n+1)| * |f n| := by rw [abs_mul]
      _ ≤ ‖f‖+‖w‖*‖f‖ := add_le_add (boundedSequence_abs_le f _)
        (mul_le_mul (boundedSequence_abs_le w _) (boundedSequence_abs_le f _)
          (abs_nonneg _) (norm_nonneg _))
      _ = (1+‖w‖)*‖f‖ := by ring

/-- The continuous linear operator I-W on bounded sequences. -/
def differenceMap (w : BoundedSequence) : BoundedSequence →L[ℝ] BoundedSequence :=
  let D : BoundedSequence →ₗ[ℝ] BoundedSequence :=
    { toFun := fun f => ofAbsBound (differenceFun w f) ((1+‖w‖)*‖f‖)
        (differenceFun_bound w f)
      map_add' := by
        intro f g
        apply BoundedContinuousFunction.ext
        intro n
        cases n with
        | zero => rfl
        | succ n =>
          change (f+g) (n+1)-w (n+1)*(f+g) n =
            (f (n+1)-w (n+1)*f n) + (g (n+1)-w (n+1)*g n)
          simp only [BoundedContinuousFunction.add_apply]
          ring
      map_smul' := by
        intro c f
        apply BoundedContinuousFunction.ext
        intro n
        cases n with
        | zero => rfl
        | succ n =>
          change c*f (n+1)-w (n+1)*(c*f n) = c*(f (n+1)-w (n+1)*f n)
          ring }
  D.mkContinuous (1+‖w‖) (by
    intro f
    apply BoundedContinuousFunction.norm_le_of_nonempty.mpr
    intro n
    exact differenceFun_bound w f n)

@[simp] theorem differenceMap_apply (w f : BoundedSequence) (n : ℕ) :
    differenceMap w f n = differenceFun w f n := rfl

theorem differenceMap_injective (w : BoundedSequence) : Function.Injective (differenceMap w) := by
  intro f g h
  apply BoundedContinuousFunction.ext
  intro n
  induction n with
  | zero =>
    have hh := congrArg (fun v : BoundedSequence => v 0) h
    exact hh
  | succ n ih =>
    have hh := congrArg (fun v : BoundedSequence => v (n+1)) h
    change f (n+1)-w (n+1)*f n = g (n+1)-w (n+1)*g n at hh
    rw [ih] at hh
    linarith

theorem difference_solution (w : BoundedSequence) (hw : ∀ n, 0 ≤ w n)
    (M : ℝ) (hM : ∀ n, rowSum w n ≤ M) (f : BoundedSequence) :
    differenceMap w (solutionMap hw M hM f) = f := by
  apply BoundedContinuousFunction.ext
  intro n
  cases n with
  | zero => rfl
  | succ n =>
    change forwardSolution w f (n+1)-w (n+1)*forwardSolution w f n = f (n+1)
    rw [forwardSolution_succ]
    ring

theorem solution_difference (w : BoundedSequence) (hw : ∀ n, 0 ≤ w n)
    (M : ℝ) (hM : ∀ n, rowSum w n ≤ M) (f : BoundedSequence) :
    solutionMap hw M hM (differenceMap w f) = f := by
  apply differenceMap_injective w
  exact difference_solution w hw M hM (differenceMap w f)

/-- The full bounded-bijection equivalence of the manuscript's weighted-shift
lemma, on the Banach space of bounded real sequences with supremum norm. -/
theorem differenceMap_bijective_iff_geometric (w : BoundedSequence) (hw : ∀ n, 0 ≤ w n) :
    Function.Bijective (differenceMap w) ↔
    (∃ C ρ : ℝ, 1 ≤ C ∧ 0 < ρ ∧ ρ < 1 ∧
      ∀ s N, blockProduct w s N ≤ C*ρ^N) := by
  constructor
  · intro hb
    let oneSeq : BoundedSequence := BoundedContinuousFunction.const ℕ 1
    obtain ⟨v, hv⟩ := hb.2 oneSeq
    have he : (v : ℕ → ℝ) = forwardSolution w (fun _ => 1) := by
      apply forwardSolution_unique
      · exact congrArg (fun g : BoundedSequence => g 0) hv
      · intro n
        exact congrArg (fun g : BoundedSequence => g (n+1)) hv
    apply geometric_of_rowSum_bound hw (M := ‖v‖)
    intro n
    calc
      rowSum w n = v n := by rw [he, forwardSolution_one]
      _ ≤ |v n| := le_abs_self _
      _ ≤ ‖v‖ := boundedSequence_abs_le v n
  · rintro ⟨C, ρ, hC, hρ0, hρ1, hg⟩
    let M := C/(1-ρ)
    have hM : ∀ n, rowSum w n ≤ M :=
      rowSum_bound_of_geometric (by linarith) hρ0.le hρ1 hg
    exact ⟨differenceMap_injective w, fun f =>
      ⟨solutionMap hw M hM f, difference_solution w hw M hM f⟩⟩

/-- The exact inverse estimate stated in the manuscript, including the unit
term corresponding to the current forcing entry. -/
theorem rowSum_sharp_bound_of_geometric {w : ℕ → ℝ} {C ρ : ℝ}
    (hC : 0 ≤ C) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hg : ∀ s N, blockProduct w s N ≤ C * ρ^N) (n : ℕ) :
    rowSum w n ≤ 1 + C*ρ/(1-ρ) := by
  rw [rowSum_eq_sum, sum_range_succ]
  simp only [Nat.sub_self, blockProduct_zero]
  have hsum : ∑ s ∈ range n, C*ρ^(n-s) = C*ρ * ∑ s ∈ range n, ρ^s := by
    calc
      ∑ s ∈ range n, C*ρ^(n-s) = ∑ s ∈ range n, (C*ρ)*ρ^(n-1-s) := by
        apply sum_congr rfl
        intro s hs
        have hsn : s < n := mem_range.mp hs
        have he : n-s = (n-1-s)+1 := by omega
        rw [he, pow_succ]
        ring
      _ = C*ρ * ∑ s ∈ range n, ρ^(n-1-s) := (mul_sum ..).symm
      _ = C*ρ * ∑ s ∈ range n, ρ^s := by rw [sum_range_reflect]
  calc
    (∑ s ∈ range n, blockProduct w s (n-s)) + 1
        ≤ (∑ s ∈ range n, C*ρ^(n-s)) + 1 :=
      by gcongr with s hs; exact hg s (n-s)
    _ = C*ρ * (∑ s ∈ range n, ρ^s) + 1 := by rw [hsum]
    _ ≤ C*ρ * (1/(1-ρ)) + 1 :=
      by
        have hh := mul_le_mul_of_nonneg_left
          (geometric_partial_sum_le hρ0 hρ1 n) (mul_nonneg hC hρ0)
        linarith
    _ = 1+C*ρ/(1-ρ) := by ring

/-- A continuous linear inverse for I-W, with both inverse identities proved
from the explicit recurrence rather than assumed. -/
def differenceEquiv (w : BoundedSequence) (hw : ∀ n, 0 ≤ w n)
    (M : ℝ) (hM : ∀ n, rowSum w n ≤ M) :
    BoundedSequence ≃L[ℝ] BoundedSequence where
  toLinearEquiv :=
    { toLinearMap := (differenceMap w).toLinearMap
      invFun := solutionMap hw M hM
      left_inv := solution_difference w hw M hM
      right_inv := difference_solution w hw M hM }
  continuous_toFun := (differenceMap w).continuous
  continuous_invFun := (solutionMap hw M hM).continuous

theorem solutionMap_norm_le {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n)
    (M : ℝ) (hM : ∀ n, rowSum w n ≤ M) : ‖solutionMap hw M hM‖ ≤ M := by
  have hMone : 1 ≤ M := by simpa using hM 0
  apply ContinuousLinearMap.opNorm_le_bound _ (by linarith)
  intro f
  apply BoundedContinuousFunction.norm_le_of_nonempty.mpr
  intro n
  change |forwardSolution w f n| ≤ M*‖f‖
  calc
    |forwardSolution w f n| ≤ ‖f‖ * rowSum w n :=
      forwardSolution_bound hw (boundedSequence_abs_le f) n
    _ ≤ ‖f‖ * M := mul_le_mul_of_nonneg_left (hM n) (norm_nonneg f)
    _ = M*‖f‖ := mul_comm _ _

/-- Inverse norm at most `1 + C*rho/(1-rho)` under the geometric bound. -/
theorem weighted_shift_inverse_norm_bound (w : BoundedSequence) (hw : ∀ n, 0 ≤ w n)
    {C ρ : ℝ} (hC : 1 ≤ C) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : ∀ s N, blockProduct w s N ≤ C * ρ^N) :
    ∃ e : BoundedSequence ≃L[ℝ] BoundedSequence,
      (∀ f, e f = differenceMap w f) ∧
      ‖e.symm.toContinuousLinearMap‖ ≤ 1+C*ρ/(1-ρ) := by
  let M := 1+C*ρ/(1-ρ)
  have hM : ∀ n, rowSum w n ≤ M :=
    rowSum_sharp_bound_of_geometric (by linarith) hρ0.le hρ1 hg
  refine ⟨differenceEquiv w hw M hM, fun _ => rfl, ?_⟩
  exact solutionMap_norm_le hw M hM

/-- Uniformly bounded weights allow a strict bound at one block length to
control products of every length. This is the fixed-block formulation in
the last sentence of the manuscript's weighted-shift lemma. -/
theorem geometric_iff_block_contraction {w : ℕ → ℝ}
    (hw : ∀ n, 0 ≤ w n) (hb : ∃ B : ℝ, ∀ n, w n ≤ B) :
    (∃ C ρ : ℝ, 1 ≤ C ∧ 0 < ρ ∧ ρ < 1 ∧
      ∀ s N, blockProduct w s N ≤ C*ρ^N) ↔
    (∃ h : ℕ, 0 < h ∧ ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧
      ∀ s, blockProduct w s h ≤ θ) := by
  constructor
  · rintro ⟨C, ρ, hC, hρ0, hρ1, hg⟩
    have hCpos : 0 < C := by linarith
    obtain ⟨h, hh⟩ := exists_pow_lt_of_lt_one (one_div_pos.mpr hCpos) hρ1
    have hθ : C*ρ^h < 1 := by
      have ht := (lt_div_iff₀ hCpos).mp hh
      nlinarith
    have hhpos : 0 < h := by
      by_contra hn
      have he : h = 0 := by omega
      simp only [he, pow_zero, mul_one] at hθ
      linarith
    exact ⟨h, hhpos, C*ρ^h, mul_nonneg hCpos.le (pow_nonneg hρ0.le _), hθ,
      fun s => hg s h⟩
  · rintro ⟨h, hh, θ, hθ0, hθ1, hc⟩
    obtain ⟨B, hB⟩ := hb
    have hB0 : 0 ≤ B := le_trans (hw 0) (hB 0)
    let t : ℝ := (1+θ)/2
    have ht0 : 0 < t := by dsimp [t]; linarith
    have ht1 : t < 1 := by dsimp [t]; linarith
    have hθt : θ ≤ t := by dsimp [t]; linarith
    let ρ : ℝ := t ^ ((h : ℝ)⁻¹)
    have hρ0 : 0 < ρ := Real.rpow_pos_of_pos ht0 _
    have hρ1 : ρ < 1 := Real.rpow_lt_one ht0.le ht1 (inv_pos.mpr (by exact_mod_cast hh))
    have hρh : ρ^h = t := Real.rpow_inv_natCast_pow ht0.le (by omega)
    let C : ℝ := ∑ j ∈ range h, B^j / ρ^j
    have hterm (j : ℕ) : 0 ≤ B^j / ρ^j :=
      div_nonneg (pow_nonneg hB0 j) (pow_nonneg hρ0.le j)
    have hC : 1 ≤ C := by
      have hs := single_le_sum (fun j (_ : j ∈ range h) => hterm j)
        (show 0 ∈ range h from mem_range.mpr hh)
      simpa [C] using hs
    have hsmall (s N : ℕ) (hN : N < h) : blockProduct w s N ≤ C*ρ^N := by
      have hprod : blockProduct w s N ≤ B^N := by
        unfold blockProduct
        calc
          ∏ i ∈ range N, w (s+i+1) ≤ ∏ _i ∈ range N, B :=
            prod_le_prod (fun i _ => hw _) (fun i _ => hB _)
          _ = B^N := by simp
      have hratio : B^N / ρ^N ≤ C := single_le_sum
        (fun j (_ : j ∈ range h) => hterm j) (mem_range.mpr hN)
      exact le_trans hprod ((div_le_iff₀ (pow_pos hρ0 N)).mp hratio)
    refine ⟨C, ρ, hC, hρ0, hρ1, ?_⟩
    intro s N
    induction N using Nat.strong_induction_on generalizing s with
    | h N ih =>
      by_cases hN : N < h
      · exact hsmall s N hN
      · have hle : h ≤ N := by omega
        have hlt : N-h < N := by omega
        have he : (N-h)+h = N := by omega
        have ih' := ih (N-h) hlt s
        have hc' : blockProduct w (s+(N-h)) h ≤ t := le_trans (hc _) hθt
        calc
          blockProduct w s N = blockProduct w s (N-h) * blockProduct w (s+(N-h)) h := by
            rw [← blockProduct_add, he]
          _ ≤ (C*ρ^(N-h))*t := mul_le_mul ih' hc'
            (blockProduct_nonneg hw _ _) (mul_nonneg (by linarith) (pow_nonneg hρ0.le _))
          _ = C*ρ^N := by rw [← hρh, mul_assoc, ← pow_add, he]

#print axioms blockProduct_add
#print axioms rowSum_eq_sum
#print axioms geometric_of_rowSum_bound
#print axioms rowSum_bounded_iff_geometric
#print axioms forwardSolution_unique
#print axioms forwardSolution_bound
#print axioms differenceMap_bijective_iff_geometric
#print axioms weighted_shift_inverse_norm_bound
#print axioms geometric_iff_block_contraction

end BTP.Stability
