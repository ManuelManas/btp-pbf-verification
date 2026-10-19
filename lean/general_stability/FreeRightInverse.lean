import FreeNeumann

noncomputable section
namespace BTP.FreeScalar
open BTP.Stability

/-- Forcing normalization for the backward recurrence. -/
def backwardForcing (u : BoundedSequence) : BoundedSequence →L[ℝ] BoundedSequence :=
  -ContinuousLinearMap.mul ℝ BoundedSequence
    ((BoundedContinuousFunction.compContinuousCLM ℝ ℝ
      ⟨fun n : ℕ => n+1, continuous_of_discreteTopology⟩) u)

@[simp] theorem backwardForcing_apply (u f : BoundedSequence) (n : ℕ) :
    backwardForcing u f n = -(u (n+1)*f n) := rfl

theorem backward_normalization (w u : BoundedSequence)
    (huw : ∀ n, u n*w n=1) (v : BoundedSequence) :
    (1-futureShift u) v = backwardForcing u (freeDifference w v) := by
  apply BoundedContinuousFunction.ext
  intro n
  change v n-u (n+1)*v (n+1) = -(u (n+1)*(v (n+1)-w (n+1)*v n))
  nlinarith only [congrArg (fun x : ℝ => x*v n) (huw (n+1))]

theorem backwardForcing_injective (u : BoundedSequence) (hu : ∀ n, u n≠0) :
    Function.Injective (backwardForcing u) := by
  intro f g he
  apply BoundedContinuousFunction.ext
  intro n
  have h := congrArg (fun v : BoundedSequence => v n) he
  rw [backwardForcing_apply, backwardForcing_apply] at h
  exact mul_left_cancel₀ (hu (n+1)) (neg_injective h)

/-- Uniform reciprocal-product decay gives a bounded right inverse of
the original free-initial-value equation, without imposing a boundary value. -/
theorem freeDifference_reciprocal_rightInverse (w u : BoundedSequence)
    (hu : ∀ n, 0<u n) (huw : ∀ n, u n*w n=1) (hg : Geometric u) :
    ∃ R : BoundedSequence →L[ℝ] BoundedSequence,
      (freeDifference w).comp R = ContinuousLinearMap.id ℝ BoundedSequence ∧
      R.comp (freeDifference w) = ContinuousLinearMap.id ℝ BoundedSequence ∧
      (∀ f ∈ cZero, R f ∈ cZero) := by
  obtain ⟨S,hS,hS',hSc⟩ := futureShift_neumann u (fun n => (hu n).le) hg
  let R := S.comp (backwardForcing u)
  have hR (f : BoundedSequence) : freeDifference w (R f) = f := by
    apply backwardForcing_injective u (fun n => (hu n).ne')
    rw [←backward_normalization w u huw]
    change ((1-futureShift u)*S) (backwardForcing u f) = _
    rw [hS]; rfl
  have hR' (v : BoundedSequence) : R (freeDifference w v) = v := by
    change S (backwardForcing u (freeDifference w v)) = v
    rw [←backward_normalization w u huw]
    change (S*(1-futureShift u)) v=v
    rw [hS']; rfl
  refine ⟨R, ContinuousLinearMap.ext hR, ContinuousLinearMap.ext hR', ?_⟩
  intro f hf
  apply hSc
  change Filter.Tendsto (fun n => -(u (n+1)*f n)) Filter.atTop (nhds 0)
  have hf' : Filter.Tendsto (fun n => f n) Filter.atTop (nhds 0) := hf
  simpa using (bdd_le_mul_tendsto_zero' ‖u‖
    (Filter.Eventually.of_forall (fun n => boundedSequence_abs_le u (n+1))) hf').neg

end BTP.FreeScalar
