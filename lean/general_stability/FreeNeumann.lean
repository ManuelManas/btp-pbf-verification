import FreeScalar
import Mathlib.Analysis.Normed.Operator.Mul

set_option maxHeartbeats 2000000

noncomputable section
open Filter Finset
open scoped Topology BigOperators
namespace BTP.FreeScalar
open BTP.Stability

theorem cZero_isClosed : IsClosed (cZero : Set BoundedSequence) := by
  apply isClosed_of_closure_subset
  intro v hv
  change Tendsto (fun n => v n) atTop (𝓝 0)
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨g,hg,hvg⟩ := Metric.mem_closure_iff.mp hv (ε/2) (by positivity)
  have hg' : Tendsto (fun n => g n) atTop (𝓝 0) := hg
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hg' (ε/2) (by positivity)
  refine ⟨N,fun n hn => ?_⟩
  have hdiff := boundedSequence_abs_le (v-g) n
  change |v n-g n| ≤ ‖v-g‖ at hdiff
  rw [dist_eq_norm] at hvg
  have hgn := hN n hn
  simp only [Real.dist_eq,sub_zero] at hgn ⊢
  calc
    |v n| = |(v n-g n)+g n| := by congr 1; ring
    _ ≤ |v n-g n|+|g n| := abs_add_le _ _
    _ < ε/2+ε/2 := add_lt_add (hdiff.trans_lt hvg) hgn
    _ = ε := by ring

theorem neumann_summable {R : Type*} [NormedRing R] [CompleteSpace R] (W : R)
    {C ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hpower : ∀ n, ‖W^n‖ ≤ C*ρ^n) : Summable (fun n : ℕ => W^n) :=
  ((summable_geometric_of_lt_one hρ hρ1).mul_left C).of_norm_bounded hpower

theorem neumann_inverses {R : Type*} [NormedRing R] (W : R)
    (hs : Summable (fun n : ℕ => W^n)) :
    (1-W)*(∑' n : ℕ, W^n) = 1 ∧ (∑' n : ℕ, W^n)*(1-W) = 1 :=
  ⟨hs.one_sub_mul_tsum_pow, hs.tsum_pow_mul_one_sub⟩

theorem neumann_preserves_cZero (W : BoundedSequence →L[ℝ] BoundedSequence)
    (hW : ∀ v ∈ cZero, W v ∈ cZero)
    (hs : Summable (fun n : ℕ => W^n)) (v : BoundedSequence) (hv : v ∈ cZero) :
    (∑' n : ℕ, W^n) v ∈ cZero := by
  have hpow (n : ℕ) : (W^n) v ∈ cZero := by
    induction n with
    | zero => simpa using hv
    | succ n ih => simpa only [pow_succ',mul_apply_eq_comp] using hW _ ih
  have hsum := (ContinuousLinearMap.apply ℝ BoundedSequence v).hasSum hs.hasSum
  apply cZero_isClosed.mem_of_tendsto hsum.tendsto_sum_nat
  exact Eventually.of_forall (fun n => cZero.sum_mem (fun k _ => hpow k))

/-- A weighted shift towards the future: its powers contain forward
window products. This is the operator used in the growing-weight case. -/
def futureShift (u : BoundedSequence) : BoundedSequence →L[ℝ] BoundedSequence :=
  (ContinuousLinearMap.mul ℝ BoundedSequence
    ((BoundedContinuousFunction.compContinuousCLM ℝ ℝ
      ⟨fun n : ℕ => n+1, continuous_of_discreteTopology⟩) u)).comp
    (BoundedContinuousFunction.compContinuousCLM ℝ ℝ
      ⟨fun n : ℕ => n+1, continuous_of_discreteTopology⟩)

@[simp] theorem futureShift_apply (u v : BoundedSequence) (n : ℕ) :
    futureShift u v n = u (n+1)*v (n+1) := rfl

theorem futureShift_pow_apply (u v : BoundedSequence) (k n : ℕ) :
    (futureShift u ^ k) v n = blockProduct u n k * v (n+k) := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_apply_eq_comp, futureShift_apply, ih,
      blockProduct_head]
    simp only [Nat.add_comm, Nat.add_left_comm]
    ring

theorem futureShift_pow_norm (u : BoundedSequence) (hu : ∀ n, 0 ≤ u n)
    {C ρ : ℝ} (hC : 0 ≤ C) (hρ : 0 ≤ ρ)
    (hg : ∀ s N, blockProduct u s N ≤ C*ρ^N) (k : ℕ) :
    ‖futureShift u ^ k‖ ≤ C*ρ^k := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC (pow_nonneg hρ k))
  intro v
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  intro n
  rw [Real.norm_eq_abs, futureShift_pow_apply, abs_mul,
    abs_of_nonneg (blockProduct_nonneg hu n k)]
  exact mul_le_mul (hg n k) (boundedSequence_abs_le v _) (abs_nonneg _) (by positivity)

theorem futureShift_preserves_cZero (u : BoundedSequence) (v : BoundedSequence)
    (hv : v ∈ cZero) : futureShift u v ∈ cZero := by
  change Tendsto (fun n => u (n+1)*v (n+1)) atTop (𝓝 0)
  have hv' : Tendsto (fun n => v n) atTop (𝓝 0) := hv
  exact bdd_le_mul_tendsto_zero' ‖u‖
    (Eventually.of_forall (fun n => boundedSequence_abs_le u (n+1)))
    (hv'.comp (tendsto_add_atTop_nat 1))

/-- The Neumann inverse acts on genuine bounded sequences, and also
preserves the genuine subspace of sequences tending to zero. -/
theorem futureShift_neumann (u : BoundedSequence) (hu : ∀ n, 0 ≤ u n)
    (hg : Geometric u) :
    ∃ S : BoundedSequence →L[ℝ] BoundedSequence,
      (1-futureShift u)*S = 1 ∧ S*(1-futureShift u) = 1 ∧
      (∀ v ∈ cZero, S v ∈ cZero) := by
  obtain ⟨C,ρ,hC,hρ,hρ1,hbound⟩ := hg
  have hs := neumann_summable (futureShift u) hρ.le hρ1
    (futureShift_pow_norm u hu (by linarith) hρ.le hbound)
  refine ⟨∑' n : ℕ, futureShift u ^ n, (neumann_inverses _ hs).1,
    (neumann_inverses _ hs).2, ?_⟩
  exact neumann_preserves_cZero _ (futureShift_preserves_cZero u) hs

end BTP.FreeScalar
