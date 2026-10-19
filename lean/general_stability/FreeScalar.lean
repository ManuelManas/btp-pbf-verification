import WeightedShift
import Mathlib.LinearAlgebra.Quotient.Basic

/-! Positive scalar difference equations with a free initial value.
The core necessity argument for `stab:lem:free-scalar-quotient` is a
bounded supersolution with a strictly positive eventual forcing term.
No dichotomy is included among the hypotheses of that argument. -/

noncomputable section
open Filter
open scoped Topology
open scoped BigOperators
namespace BTP.FreeScalar
open BTP.Stability

def Geometric (w : ℕ → ℝ) : Prop :=
  ∃ C ρ : ℝ, 1 ≤ C ∧ 0 < ρ ∧ ρ < 1 ∧
    ∀ s N, blockProduct w s N ≤ C * ρ^N

theorem blockProduct_shift (w : ℕ → ℝ) (r s N : ℕ) :
    blockProduct (fun n => w (r+n)) s N = blockProduct w (r+s) N := by
  simp only [blockProduct, Nat.add_assoc]

theorem blockProduct_head (w : ℕ → ℝ) (s N : ℕ) :
    blockProduct w s (N+1) = w (s+1) * blockProduct w (s+1) N := by
  rw [show N+1=1+N by omega, blockProduct_add]
  simp [blockProduct]

/-- A finite initial segment never affects uniform exponential decay. -/
theorem geometric_prepend {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n)
    (hg : Geometric (fun n => w (1+n))) : Geometric w := by
  obtain ⟨C,ρ,hC,hρ,hρ1,hbound⟩ := hg
  let K := 1+w 1/ρ
  have hK : 1 ≤ K := by dsimp [K]; have := div_nonneg (hw 1) hρ.le; linarith
  have hC0 : 0 ≤ C := by linarith
  have hKρ : w 1 ≤ K*ρ := by
    dsimp [K]
    have he : (1+w 1/ρ)*ρ = ρ+w 1 := by field_simp
    rw [he]; linarith
  refine ⟨C*K,ρ,le_trans hC (le_mul_of_one_le_right hC0 hK),hρ,hρ1,?_⟩
  intro s N
  cases s with
  | succ s =>
    have hh := hbound s N
    rw [blockProduct_shift] at hh
    have hc : C*ρ^N ≤ C*K*ρ^N :=
      mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hC0 hK) (pow_nonneg hρ.le N)
    have hb : blockProduct w (s+1) N ≤ C*ρ^N := by simpa only [Nat.add_comm] using hh
    exact hb.trans hc
  | zero =>
    cases N with
    | zero => simp only [blockProduct_zero,pow_zero,mul_one]; exact le_trans hC (le_mul_of_one_le_right hC0 hK)
    | succ N =>
      rw [blockProduct_head]
      have hh := hbound 0 N
      rw [blockProduct_shift] at hh
      simp only [Nat.add_zero] at hh
      have h1 := mul_le_mul_of_nonneg_left hh (hw 1)
      have h2 := mul_le_mul_of_nonneg_right hKρ (mul_nonneg hC0 (pow_nonneg hρ.le N))
      simp only [Nat.zero_add]
      calc
        w 1 * blockProduct w 1 N ≤ w 1*(C*ρ^N) := h1
        _ ≤ (K*ρ)*(C*ρ^N) := h2
        _ = C*K*ρ^(N+1) := by rw [pow_succ]; ring

theorem geometric_of_shift {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n) (r : ℕ)
    (hg : Geometric (fun n => w (r+n))) : Geometric w := by
  induction r with
  | zero => simpa using hg
  | succ r ih =>
    apply ih
    apply geometric_prepend (w := fun n => w (r+n)) (fun n => hw _)
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hg

theorem forward_potential {w V : ℕ → ℝ} {δ M ρ : ℝ}
    (hw : ∀ n, 0 ≤ w n) (hδ : 0 < δ) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hlo : ∀ n, δ ≤ V n) (hhi : ∀ n, V n ≤ M)
    (hstep : ∀ n, w (n+1) * V n ≤ ρ * V (n+1)) : Geometric w := by
  have hM : δ ≤ M := (hlo 0).trans (hhi 0)
  have scaled (s N : ℕ) : blockProduct w s N * V s ≤ ρ^N * V (s+N) := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [blockProduct_succ, pow_succ]
      have h1 := mul_le_mul_of_nonneg_left ih (hw (s+N+1))
      have h2 := mul_le_mul_of_nonneg_left (hstep (s+N)) (pow_nonneg hρ.le N)
      calc
        blockProduct w s N * w (s+N+1) * V s
          = w (s+N+1) * (blockProduct w s N * V s) := by ring
        _ ≤ w (s+N+1) * (ρ^N * V (s+N)) := h1
        _ = ρ^N * (w (s+N+1) * V (s+N)) := by ring
        _ ≤ ρ^N * (ρ * V (s+N+1)) := h2
        _ = ρ^N * ρ * V (s+(N+1)) := by simp only [Nat.add_assoc]; ring
  refine ⟨M/δ, ρ, (one_le_div hδ).mpr hM, hρ, hρ1, ?_⟩
  intro s N
  apply (mul_le_mul_iff_left₀ hδ).mp
  calc
    blockProduct w s N * δ ≤ blockProduct w s N * V s :=
      mul_le_mul_of_nonneg_left (hlo s) (blockProduct_nonneg hw s N)
    _ ≤ ρ^N * V (s+N) := scaled s N
    _ ≤ ρ^N * M := mul_le_mul_of_nonneg_left (hhi _) (pow_nonneg hρ.le N)
    _ = (M/δ*ρ^N)*δ := by field_simp

theorem backward_potential {w V : ℕ → ℝ} {δ M ρ : ℝ}
    (hw : ∀ n, 0 ≤ w n) (hδ : 0 < δ) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hlo : ∀ n, δ ≤ V n) (hhi : ∀ n, V n ≤ M)
    (hstep : ∀ n, w (n+1) * V (n+1) ≤ ρ * V n) : Geometric w := by
  have hM : δ ≤ M := (hlo 0).trans (hhi 0)
  have scaled (s N : ℕ) : blockProduct w s N * V (s+N) ≤ ρ^N * V s := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [blockProduct_succ, pow_succ]
      have h1 := mul_le_mul_of_nonneg_left (hstep (s+N)) (blockProduct_nonneg hw s N)
      have h2 := mul_le_mul_of_nonneg_left ih hρ.le
      calc
        blockProduct w s N * w (s+N+1) * V (s+(N+1))
          = blockProduct w s N * (w (s+N+1) * V (s+N+1)) := by simp only [Nat.add_assoc]; ring
        _ ≤ blockProduct w s N * (ρ * V (s+N)) := h1
        _ = ρ * (blockProduct w s N * V (s+N)) := by ring
        _ ≤ ρ * (ρ^N * V s) := h2
        _ = ρ^N * ρ * V s := by ring
  refine ⟨M/δ, ρ, (one_le_div hδ).mpr hM, hρ, hρ1, ?_⟩
  intro s N
  apply (mul_le_mul_iff_left₀ hδ).mp
  calc
    blockProduct w s N * δ ≤ blockProduct w s N * V (s+N) :=
      mul_le_mul_of_nonneg_left (hlo _) (blockProduct_nonneg hw s N)
    _ ≤ ρ^N * V s := scaled s N
    _ ≤ ρ^N * M := mul_le_mul_of_nonneg_left (hhi _) (pow_nonneg hρ.le N)
    _ = (M/δ*ρ^N)*δ := by field_simp

theorem geometric_of_positive_supersolution {w v : ℕ → ℝ} {δ M : ℝ}
    (hw : ∀ n, 0 ≤ w n) (hδ : 0 < δ)
    (hlo : ∀ n, δ ≤ v n) (hhi : ∀ n, v n ≤ M)
    (hforce : ∀ n, δ ≤ v (n+1) - w (n+1) * v n) : Geometric w := by
  have hM : 0 < M := hδ.trans_le ((hlo 0).trans (hhi 0))
  let ρ := 1 - δ/(M+δ)
  have hd : 0 < M+δ := by positivity
  have hρ0 : 0 < ρ := by dsimp [ρ]; have := (div_lt_one hd).mpr (show δ < M+δ by linarith); linarith
  have hρ1 : ρ < 1 := by dsimp [ρ]; have := div_pos hδ hd; linarith
  apply forward_potential hw hδ hρ0 hρ1 hlo hhi
  intro n
  have hv : v (n+1)/(M+δ) ≤ 1 := (div_le_one hd).mpr (by linarith [hhi (n+1)])
  have hm := mul_le_mul_of_nonneg_left hv hδ.le
  dsimp [ρ]
  simp only [div_eq_mul_inv] at hm ⊢
  nlinarith [hforce n]

theorem reciprocal_geometric_of_negative_supersolution {w v : ℕ → ℝ} {δ M : ℝ}
    (hw : ∀ n, 0 < w n) (hδ : 0 < δ) (hM : 0 < M)
    (hlo : ∀ n, -M ≤ v n) (hhi : ∀ n, v n < 0)
    (hforce : ∀ n, δ ≤ v (n+1) - w (n+1) * v n) :
    Geometric (fun n => (w n)⁻¹) := by
  let V : ℕ → ℝ := fun n => δ-v n
  let ρ := M/(δ+M)
  have hd : 0 < δ+M := by positivity
  have hρ0 : 0 < ρ := div_pos hM hd
  have hρ1 : ρ < 1 := (div_lt_one hd).mpr (by linarith)
  have hVlo : ∀ n, δ ≤ V n := fun n => by dsimp [V]; linarith [hhi n]
  have hVhi : ∀ n, V n ≤ δ+M := fun n => by dsimp [V]; linarith [hlo n]
  apply backward_potential (fun n => (inv_pos.mpr (hw n)).le) hδ hρ0 hρ1 hVlo hVhi
  intro n
  have h1 : (w (n+1))⁻¹ * V (n+1) ≤ -v n := by
    rw [inv_mul_eq_div]
    apply (div_le_iff₀ (hw _)).mpr
    dsimp [V]
    nlinarith [hforce n]
  have h2 : -v n ≤ ρ * V n := by
    dsimp [ρ, V]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hd).mpr
    nlinarith [hlo n]
  exact h1.trans h2

theorem nonnegative_propagates {w v : ℕ → ℝ} {δ : ℝ} (hw : ∀ n, 0 ≤ w n)
    (hδ : 0 < δ) (hforce : ∀ n, δ ≤ v (n+1)-w (n+1)*v n)
    {r : ℕ} (hr : 0 ≤ v r) (k : ℕ) : δ ≤ v (r+k+1) := by
  induction k with
  | zero =>
    have h := mul_nonneg (hw (r+1)) hr
    simpa using (show δ ≤ v (r+1) by linarith [hforce r])
  | succ k ih =>
    have h := mul_nonneg (hw (r+k+1+1)) (hδ.le.trans ih)
    have hf := hforce (r+k+1)
    have : δ ≤ v (r+k+1+1) := by linarith
    simpa only [Nat.add_assoc] using this

/-- Surjectivity modulo c₀ supplies such a bounded supersolution after a
finite shift. The sign argument proves a dichotomy, rather than assuming it. -/
theorem supersolution_tail_dichotomy {w v : ℕ → ℝ} {δ M : ℝ}
    (hw : ∀ n, 0 < w n) (hδ : 0 < δ) (hM : 0 < M)
    (hv : ∀ n, |v n| ≤ M)
    (hforce : ∀ n, δ ≤ v (n+1)-w (n+1)*v n) :
    (∃ r, Geometric (fun n => w (r+n))) ∨ Geometric (fun n => (w n)⁻¹) := by
  by_cases hpos : ∃ r, 0 ≤ v r
  · obtain ⟨r, hr⟩ := hpos
    left
    refine ⟨r+1, ?_⟩
    apply geometric_of_positive_supersolution (v := fun n => v (r+1+n))
      (δ := δ) (M := M) (fun n => (hw _).le) hδ
    · intro n
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        nonnegative_propagates (fun n => (hw n).le) hδ hforce hr n
    · intro n; exact (abs_le.mp (hv _)).2
    · intro n; simpa only [Nat.add_assoc] using hforce (r+1+n)
  · right
    apply reciprocal_geometric_of_negative_supersolution hw hδ hM
      (fun n => (abs_le.mp (hv n)).1) (fun n => ?_) hforce
    exact lt_of_not_ge (fun h => hpos ⟨n,h⟩)

theorem supersolution_dichotomy {w v : ℕ → ℝ} {δ M : ℝ}
    (hw : ∀ n, 0 < w n) (hδ : 0 < δ) (hM : 0 < M)
    (hv : ∀ n, |v n| ≤ M)
    (hforce : ∀ n, δ ≤ v (n+1)-w (n+1)*v n) :
    Geometric w ∨ Geometric (fun n => (w n)⁻¹) := by
  rcases supersolution_tail_dichotomy hw hδ hM hv hforce with ⟨r,hr⟩|hr
  · exact Or.inl (geometric_of_shift (fun n => (hw n).le) r hr)
  · exact Or.inr hr

theorem eventual_supersolution_dichotomy {w v : ℕ → ℝ} {δ M : ℝ}
    (hw : ∀ n, 0 < w n) (hδ : 0 < δ) (hM : 0 < M)
    (hv : ∀ n, |v n| ≤ M) (r : ℕ)
    (hforce : ∀ n, r ≤ n → δ ≤ v (n+1)-w (n+1)*v n) :
    Geometric w ∨ Geometric (fun n => (w n)⁻¹) := by
  have hs := supersolution_dichotomy
    (w := fun n => w (r+n)) (v := fun n => v (r+n))
    (fun n => hw _) hδ hM (fun n => hv _) (fun n => by
      simpa only [Nat.add_assoc] using hforce (r+n) (by omega))
  rcases hs with hs|hs
  · exact Or.inl (geometric_of_shift (fun n => (hw n).le) r hs)
  · exact Or.inr (geometric_of_shift (fun n => (inv_pos.mpr (hw n)).le) r hs)

/-- The genuine subspace c₀ of bounded sequences that converge to zero. -/
def cZero : Submodule ℝ BoundedSequence where
  carrier := {v | Tendsto (fun n => v n) atTop (𝓝 0)}
  zero_mem' := tendsto_const_nhds
  add_mem' := by intro a b ha hb; simpa using ha.add hb
  smul_mem' := by intro c v hv; simpa using hv.const_mul c

/-- The free-initial-value difference map, with output indexed from the
first recurrence row. Unlike differenceMap, no equation fixes v(0). -/
def freeDifference (w : BoundedSequence) : BoundedSequence →L[ℝ] BoundedSequence :=
  (BoundedContinuousFunction.compContinuousCLM ℝ ℝ
    ⟨fun n : ℕ => n+1, continuous_of_discreteTopology⟩).comp (differenceMap w)

@[simp] theorem freeDifference_apply (w v : BoundedSequence) (n : ℕ) :
    freeDifference w v n = v (n+1)-w (n+1)*v n := rfl

theorem freeDifference_preserves_cZero (w : BoundedSequence) :
    cZero ≤ cZero.comap (freeDifference w).toLinearMap := by
  intro v hv
  change Tendsto (fun n => freeDifference w v n) atTop (𝓝 0)
  have hv' : Tendsto (fun n => v n) atTop (𝓝 0) := hv
  have hshift : Tendsto (fun n => v (n+1)) atTop (𝓝 0) := hv'.comp (tendsto_add_atTop_nat 1)
  have hmul := bdd_le_mul_tendsto_zero' ‖w‖
    (f := fun n => w (n+1)) (g := fun n => v n)
    (Filter.Eventually.of_forall (fun n => boundedSequence_abs_le w (n+1))) hv'
  simpa using hshift.sub hmul

def quotientDifference (w : BoundedSequence) :
    (BoundedSequence ⧸ cZero) →ₗ[ℝ] (BoundedSequence ⧸ cZero) :=
  cZero.mapQ cZero (freeDifference w).toLinearMap (freeDifference_preserves_cZero w)

/-- Necessity in the actual quotient ℓ∞/c₀: surjectivity forces uniform
geometric decay in one of the two directions. -/
theorem quotient_surjective_implies_dichotomy (w : BoundedSequence)
    (hw : ∀ n, 0 < w n) (hs : Function.Surjective (quotientDifference w)) :
    Geometric w ∨ Geometric (fun n => (w n)⁻¹) := by
  obtain ⟨vclass,hvclass⟩ := hs (Submodule.Quotient.mk (1 : BoundedSequence))
  obtain ⟨v,rfl⟩ := Submodule.Quotient.mk_surjective cZero vclass
  change Submodule.Quotient.mk (freeDifference w v) = Submodule.Quotient.mk (1 : BoundedSequence) at hvclass
  have hz : freeDifference w v - 1 ∈ cZero := (Submodule.Quotient.eq cZero).mp hvclass
  have ht : Tendsto (fun n => freeDifference w v n-1) atTop (𝓝 0) := hz
  have he : ∀ᶠ n in atTop, -(1/2 : ℝ) < freeDifference w v n-1 :=
    ht.eventually (Ioi_mem_nhds (by norm_num))
  obtain ⟨r,hr⟩ := eventually_atTop.mp he
  apply eventual_supersolution_dichotomy (v := v) hw (δ := 1/2) (M := ‖v‖+1)
    (by norm_num) (by positivity) (fun n => le_trans (boundedSequence_abs_le v n) (by linarith)) r
  intro n hn
  have hh := hr n hn
  rw [freeDifference_apply] at hh
  linarith

end BTP.FreeScalar
