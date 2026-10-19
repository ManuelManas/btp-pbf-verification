import FreeRightInverse
import AnalyticFactorization

noncomputable section
set_option maxHeartbeats 800000
open Filter
open scoped Topology
namespace BTP.FreeScalar
open BTP.Stability
open BTP.GeneralStability

def pastShift (w : BoundedSequence) : BoundedSequence →L[ℝ] BoundedSequence :=
  1 - differenceMap w

@[simp] theorem pastShift_zero (w v : BoundedSequence) : pastShift w v 0 = 0 := by
  change v 0-v 0=0
  ring

@[simp] theorem pastShift_succ (w v : BoundedSequence) (n : ℕ) :
    pastShift w v (n+1) = w (n+1)*v n := by
  change v (n+1)-(v (n+1)-w (n+1)*v n)=_
  ring

theorem pastShift_pow_apply (w v : BoundedSequence) (k n : ℕ) :
    (pastShift w ^ k) v n =
      if k ≤ n then blockProduct w (n-k) k * v (n-k) else 0 := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_apply_eq_comp]
    cases n with
    | zero => simp
    | succ n =>
      rw [pastShift_succ, ih]
      by_cases hk : k ≤ n
      · rw [ite_eq_left hk, ite_eq_left (by omega)]
        have hsub : n+1-(k+1)=n-k := by omega
        rw [hsub,blockProduct_succ]
        have hlast : n-k+k+1=n+1 := by omega
        rw [hlast]
        ring
      · rw [ite_eq_right hk, ite_eq_right (by omega),mul_zero]

theorem pastShift_pow_norm (w : BoundedSequence) (hw : ∀ n, 0 ≤ w n)
    {C ρ : ℝ} (hC : 0 ≤ C) (hρ : 0 ≤ ρ)
    (hg : ∀ s N, blockProduct w s N ≤ C*ρ^N) (k : ℕ) :
    ‖pastShift w ^ k‖ ≤ C*ρ^k := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC (pow_nonneg hρ k))
  intro v
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  intro n
  rw [Real.norm_eq_abs,pastShift_pow_apply]
  split_ifs
  · rw [abs_mul,abs_of_nonneg (blockProduct_nonneg hw _ _)]
    exact mul_le_mul (hg _ _) (boundedSequence_abs_le v _) (abs_nonneg _) (by positivity)
  · simp only [abs_zero]
    positivity

theorem pastShift_preserves_cZero (w v : BoundedSequence) (hv : v ∈ cZero) :
    pastShift w v ∈ cZero := by
  have hv' : Tendsto (fun n => v n) atTop (𝓝 0) := hv
  have ht := bdd_le_mul_tendsto_zero' ‖w‖
    (Eventually.of_forall (fun n => boundedSequence_abs_le w n))
    (hv'.comp (tendsto_sub_atTop_nat 1))
  change Tendsto (fun n => pastShift w v n) atTop (𝓝 0)
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
  simp

theorem pastShift_neumann (w : BoundedSequence) (hw : ∀ n, 0 ≤ w n)
    (hg : Geometric w) :
    ∃ S : BoundedSequence →L[ℝ] BoundedSequence,
      (differenceMap w).comp S = ContinuousLinearMap.id ℝ BoundedSequence ∧
      S.comp (differenceMap w) = ContinuousLinearMap.id ℝ BoundedSequence ∧
      (∀ v ∈ cZero, S v ∈ cZero) := by
  obtain ⟨C,ρ,hC,hρ,hρ1,hbound⟩ := hg
  have hs := neumann_summable (pastShift w) hρ.le hρ1
    (pastShift_pow_norm w hw (by linarith) hρ.le hbound)
  have hneumann := neumann_inverses (pastShift w) hs
  have hd : 1-pastShift w=differenceMap w := by dsimp [pastShift]; abel
  rw [hd] at hneumann
  refine ⟨∑' n : ℕ, pastShift w ^ n, hneumann.1, hneumann.2, ?_⟩
  exact neumann_preserves_cZero _ (pastShift_preserves_cZero w) hs

theorem zeroExtension_preserves_cZero (k : ℕ) (v : BoundedSequence) (hv : v ∈ cZero) :
    zeroExtension k v ∈ cZero := by
  have hv' : Tendsto (fun n => v n) atTop (𝓝 0) := hv
  change Tendsto (fun n => zeroExtension k v n) atTop (𝓝 0)
  apply (hv'.comp (tendsto_sub_atTop_nat k)).congr'
  filter_upwards [eventually_ge_atTop k] with n hn
  simp [initialExtension,hn]

theorem freeDifference_forward_rightInverse (w : BoundedSequence)
    (hw : ∀ n, 0 ≤ w n) (hg : Geometric w) :
    ∃ R : BoundedSequence →L[ℝ] BoundedSequence,
      (freeDifference w).comp R = ContinuousLinearMap.id ℝ BoundedSequence ∧
      (∀ f ∈ cZero, R f ∈ cZero) := by
  obtain ⟨S,hS,_,hSc⟩ := pastShift_neumann w hw hg
  let R := S.comp (zeroExtension 1)
  refine ⟨R, ?_, fun f hf => hSc _ (zeroExtension_preserves_cZero 1 f hf)⟩
  apply ContinuousLinearMap.ext
  intro f
  apply BoundedContinuousFunction.ext
  intro n
  have he := congrArg (fun A : BoundedSequence →L[ℝ] BoundedSequence => A (zeroExtension 1 f) (n+1)) hS
  change freeDifference w (S (zeroExtension 1 f)) n = f n
  change differenceMap w (S (zeroExtension 1 f)) (n+1) = f n
  simpa [initialExtension] using he

theorem forward_homogeneous_cZero (w v : BoundedSequence)
    (hw : ∀ n, 0 ≤ w n) (hg : Geometric w) (hv : freeDifference w v=0) :
    v ∈ cZero := by
  obtain ⟨C,ρ,hC,hρ,hρ1,hbound⟩ := hg
  have he (n : ℕ) : v n=blockProduct w 0 n*v 0 := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hn := congrArg (fun f : BoundedSequence => f n) hv
      rw [freeDifference_apply] at hn
      change v (n+1)-w (n+1)*v n=0 at hn
      rw [blockProduct_succ,ih] at *
      simp only [Nat.zero_add]
      nlinarith only [hn]
  change Tendsto (fun n => v n) atTop (𝓝 0)
  apply squeeze_zero_norm (a := fun n => C*ρ^n*|v 0|)
  · intro n
    rw [Real.norm_eq_abs,he,abs_mul,abs_of_nonneg (blockProduct_nonneg hw 0 n)]
    exact mul_le_mul_of_nonneg_right (hbound 0 n) (abs_nonneg _)
  · have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one hρ.le hρ1).const_mul C
    simpa using ht.mul_const |v 0|

theorem forward_preimage_cZero (w : BoundedSequence) (hw : ∀ n, 0 ≤ w n)
    (hg : Geometric w) (v : BoundedSequence) (hv : freeDifference w v ∈ cZero) :
    v ∈ cZero := by
  obtain ⟨R,hR,hRc⟩ := freeDifference_forward_rightInverse w hw hg
  have hhom : freeDifference w (v-R (freeDifference w v))=0 := by
    rw [map_sub]
    have he := congrArg (fun A : BoundedSequence →L[ℝ] BoundedSequence => A (freeDifference w v)) hR
    change freeDifference w (R (freeDifference w v))=freeDifference w v at he
    rw [he,sub_self]
  have hh := forward_homogeneous_cZero w _ hw hg hhom
  have hr := hRc _ hv
  have he : v=(v-R (freeDifference w v))+R (freeDifference w v) := by abel
  rw [he]
  exact cZero.add_mem hh hr

theorem quotientDifference_bijective_of_rightInverse (w : BoundedSequence)
    (R : BoundedSequence →L[ℝ] BoundedSequence)
    (hR : (freeDifference w).comp R = ContinuousLinearMap.id ℝ BoundedSequence)
    (hpre : ∀ v : BoundedSequence, freeDifference w v ∈ cZero → v ∈ cZero) :
    Function.Bijective (quotientDifference w) := by
  constructor
  · intro x y hxy
    obtain ⟨v,rfl⟩ := Submodule.Quotient.mk_surjective cZero x
    obtain ⟨u,rfl⟩ := Submodule.Quotient.mk_surjective cZero y
    apply (Submodule.Quotient.eq cZero).mpr
    apply hpre
    rw [map_sub]
    exact (Submodule.Quotient.eq cZero).mp hxy
  · intro y
    obtain ⟨f,rfl⟩ := Submodule.Quotient.mk_surjective cZero y
    refine ⟨Submodule.Quotient.mk (R f), ?_⟩
    change Submodule.Quotient.mk (freeDifference w (R f))=Submodule.Quotient.mk f
    have he := congrArg (fun A : BoundedSequence →L[ℝ] BoundedSequence => A f) hR
    exact congrArg Submodule.Quotient.mk he

/-- In the genuine quotient of bounded sequences by sequences tending
to zero, either direction of uniform geometric decay gives a bijection. -/
theorem quotientDifference_bijective_of_dichotomy (w u : BoundedSequence)
    (hw : ∀ n, 0 < w n) (hu : ∀ n, 0 < u n) (huw : ∀ n, u n*w n=1)
    (hg : Geometric w ∨ Geometric u) :
    Function.Bijective (quotientDifference w) := by
  rcases hg with hg | hg
  · obtain ⟨R,hR,_⟩ := freeDifference_forward_rightInverse w (fun n => (hw n).le) hg
    exact quotientDifference_bijective_of_rightInverse w R hR
      (forward_preimage_cZero w (fun n => (hw n).le) hg)
  · obtain ⟨R,hR,hR',hRc⟩ := freeDifference_reciprocal_rightInverse w u hu huw hg
    apply quotientDifference_bijective_of_rightInverse w R hR
    intro v hv
    have hr := hRc _ hv
    have he := congrArg (fun A : BoundedSequence →L[ℝ] BoundedSequence => A v) hR'
    change R (freeDifference w v)=v at he
    rwa [he] at hr

#print axioms freeDifference_forward_rightInverse
#print axioms forward_preimage_cZero
#print axioms quotientDifference_bijective_of_dichotomy

end BTP.FreeScalar
