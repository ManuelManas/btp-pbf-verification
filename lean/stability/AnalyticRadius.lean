import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic

/-!
# Quantitative perturbation radius: the Banach-space argument

This file formalizes the contraction argument in the manuscript proposition
`stab:rem:general-radius`. The spaces of variations and data may differ. The
linearized multiplication is represented by a continuous linear equivalence.
The quadratic remainder and its Lipschitz bound are explicit hypotheses.
The combinatorial proof of these bounds for bidiagonal multiplication, and
real analyticity of the resulting choice, are NOT claimed in this file.
-/

namespace PBFStability

open scoped NNReal

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The fixed-point map for `D h + R h = e`. -/
def perturbationMap (D : X ≃L[ℝ] Y) (R : X → Y) (e : Y) (h : X) : X :=
  D.symm (e - R h)

theorem perturbationMap_fixed_iff (D : X ≃L[ℝ] Y) (R : X → Y) (e : Y) (h : X) :
    perturbationMap D R e h = h ↔ D h + R h = e := by
  constructor
  · intro hf
    have hh := congrArg D hf
    simp only [perturbationMap, D.apply_symm_apply] at hh
    rw [← hh]
    abel
  · intro he
    apply D.injective
    simp only [perturbationMap, D.apply_symm_apply]
    rw [← he]
    abel

theorem perturbationMap_bound (D : X ≃L[ℝ] Y) (R : X → Y)
    {M C r : ℝ} (hM : 0 < M) (hr : 0 ≤ r)
    (hsmall : M * C * r ≤ 1 / 4)
    (hD : ∀ y, ‖D.symm y‖ ≤ M * ‖y‖)
    (hR : ∀ h, ‖h‖ ≤ r → ‖R h‖ ≤ C * r ^ 2)
    {e : Y} (he : ‖e‖ ≤ r / (2 * M)) {h : X} (hh : ‖h‖ ≤ r) :
    ‖perturbationMap D R e h‖ ≤ 3 * r / 4 := by
  have hdata : M * ‖e‖ ≤ r / 2 := by
    have := (le_div_iff₀ (by positivity : 0 < 2 * M)).mp he
    nlinarith
  have hquad : M * (C * r ^ 2) ≤ r / 4 := by
    have := mul_le_mul_of_nonneg_right hsmall hr
    nlinarith
  calc
    ‖perturbationMap D R e h‖ ≤ M * ‖e - R h‖ := hD _
    _ ≤ M * (‖e‖ + ‖R h‖) := mul_le_mul_of_nonneg_left (norm_sub_le _ _) hM.le
    _ ≤ M * (‖e‖ + C * r ^ 2) := by gcongr; exact hR h hh
    _ ≤ 3 * r / 4 := by nlinarith

theorem perturbationMap_contraction (D : X ≃L[ℝ] Y) (R : X → Y)
    {M C r : ℝ} (hM : 0 < M) (hsmall : M * C * r ≤ 1 / 4)
    (hD : ∀ y, ‖D.symm y‖ ≤ M * ‖y‖)
    (hR : ∀ h, ‖h‖ ≤ r → ∀ k, ‖k‖ ≤ r →
      ‖R h - R k‖ ≤ 2 * C * r * ‖h - k‖)
    (e : Y) {h k : X} (hh : ‖h‖ ≤ r) (hk : ‖k‖ ≤ r) :
    ‖perturbationMap D R e h - perturbationMap D R e k‖ ≤
      (1 / 2 : ℝ) * ‖h - k‖ := by
  have hdiff : (e - R h) - (e - R k) = R k - R h := by abel
  calc
    ‖perturbationMap D R e h - perturbationMap D R e k‖
        = ‖D.symm (R k - R h)‖ := by
          simp only [perturbationMap, ← map_sub, hdiff]
    _ ≤ M * ‖R k - R h‖ := hD _
    _ = M * ‖R h - R k‖ := by rw [norm_sub_rev]
    _ ≤ M * (2 * C * r * ‖h - k‖) :=
      mul_le_mul_of_nonneg_left (hR h hh k hk) hM.le
    _ ≤ (1 / 2 : ℝ) * ‖h - k‖ := by
      have := mul_le_mul_of_nonneg_right hsmall (norm_nonneg (h - k))
      nlinarith

/-- The quantitative contraction theorem used by the perturbation-radius
proposition. It gives a unique solution in the full closed variation ball. -/
theorem quantitative_radius [CompleteSpace X]
    (D : X ≃L[ℝ] Y) (R : X → Y)
    {M C r : ℝ} (hM : 0 < M) (hr : 0 ≤ r)
    (hsmall : M * C * r ≤ 1 / 4)
    (hD : ∀ y, ‖D.symm y‖ ≤ M * ‖y‖)
    (hquad : ∀ h, ‖h‖ ≤ r → ‖R h‖ ≤ C * r ^ 2)
    (hlip : ∀ h, ‖h‖ ≤ r → ∀ k, ‖k‖ ≤ r →
      ‖R h - R k‖ ≤ 2 * C * r * ‖h - k‖)
    {e : Y} (he : ‖e‖ ≤ r / (2 * M)) :
    ∃! h : X, ‖h‖ ≤ r ∧ D h + R h = e := by
  let S := Metric.closedBall (0 : X) r
  have hmem (h : X) : h ∈ S ↔ ‖h‖ ≤ r := by
    simp only [S, Metric.mem_closedBall, dist_zero_right]
  have : CompleteSpace S := Metric.isClosed_closedBall.isComplete.completeSpace_coe
  have : Nonempty S := ⟨⟨0, (hmem 0).mpr (by simpa using hr)⟩⟩
  have hmap (h : S) : perturbationMap D R e h ∈ S := by
    apply (hmem _).mpr
    have hh := perturbationMap_bound D R hM hr hsmall hD hquad he
      ((hmem h).mp h.property)
    linarith
  let F : S → S := fun h => ⟨perturbationMap D R e h, hmap h⟩
  have hcontract : ContractingWith (1 / 2) F := by
    constructor
    · norm_num
    · apply LipschitzWith.of_dist_le_mul
      intro h k
      simp only [Subtype.dist_eq, dist_eq_norm]
      change ‖perturbationMap D R e h - perturbationMap D R e k‖ ≤
        ((1 / 2 : ℝ≥0) : ℝ) * ‖(h : X) - (k : X)‖
      norm_num only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
      exact perturbationMap_contraction D R hM hsmall hD hlip e
        ((hmem h).mp h.property) ((hmem k).mp k.property)
  let h : S := hcontract.fixedPoint F
  have hfix : perturbationMap D R e h = h :=
    congrArg Subtype.val (hcontract.fixedPoint_isFixedPt)
  refine ⟨h, ⟨(hmem h).mp h.property,
    (perturbationMap_fixed_iff D R e h).mp hfix⟩, ?_⟩
  intro k hk
  let ks : S := ⟨k, (hmem k).mpr hk.1⟩
  have hkfix : Function.IsFixedPt F ks := by
    apply Subtype.ext
    exact (perturbationMap_fixed_iff D R e k).mpr hk.2
  exact congrArg Subtype.val (hcontract.fixedPoint_unique hkfix)

/-- Solutions selected in the radius ball vary with Lipschitz constant `2 M`. -/
theorem quantitative_radius_lipschitz (D : X ≃L[ℝ] Y) (R : X → Y)
    {M C r : ℝ} (hM : 0 < M) (hsmall : M * C * r ≤ 1 / 4)
    (hD : ∀ y, ‖D.symm y‖ ≤ M * ‖y‖)
    (hlip : ∀ h, ‖h‖ ≤ r → ∀ k, ‖k‖ ≤ r →
      ‖R h - R k‖ ≤ 2 * C * r * ‖h - k‖)
    {e f : Y} {h k : X} (hh : ‖h‖ ≤ r) (hk : ‖k‖ ≤ r)
    (heq : D h + R h = e) (hfeq : D k + R k = f) :
    ‖h - k‖ ≤ 2 * M * ‖e - f‖ := by
  have hefix := (perturbationMap_fixed_iff D R e h).mpr heq
  have hffix := (perturbationMap_fixed_iff D R f k).mpr hfeq
  have hc := perturbationMap_contraction D R hM hsmall hD hlip e hh hk
  rw [hefix] at hc
  have hdiff : (e - R k) - (f - R k) = e - f := by abel
  have hd : ‖perturbationMap D R e k - k‖ ≤ M * ‖e - f‖ := by
    have hd' : ‖perturbationMap D R e k - perturbationMap D R f k‖ ≤
        M * ‖e - f‖ := by
      simpa only [perturbationMap, ← map_sub, hdiff] using hD (e - f)
    rwa [hffix] at hd'
  have ht : ‖h - k‖ ≤ ‖h - perturbationMap D R e k‖ +
      ‖perturbationMap D R e k - k‖ := by
    calc
      ‖h - k‖ = ‖(h - perturbationMap D R e k) +
          (perturbationMap D R e k - k)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  linarith

/-- The norm of the solution actually stays within `3r/4`. -/
theorem quantitative_radius_solution_bound (D : X ≃L[ℝ] Y) (R : X → Y)
    {M C r : ℝ} (hM : 0 < M) (hr : 0 ≤ r)
    (hsmall : M * C * r ≤ 1 / 4)
    (hD : ∀ y, ‖D.symm y‖ ≤ M * ‖y‖)
    (hquad : ∀ h, ‖h‖ ≤ r → ‖R h‖ ≤ C * r ^ 2)
    {e : Y} (he : ‖e‖ ≤ r / (2 * M)) {h : X}
    (hh : ‖h‖ ≤ r) (heq : D h + R h = e) :
    ‖h‖ ≤ 3 * r / 4 := by
  have := perturbationMap_bound D R hM hr hsmall hD hquad he hh
  rwa [(perturbationMap_fixed_iff D R e h).mpr heq] at this

/-- The radius condition as stated in the manuscript implies the condition
used in the contraction estimates. -/
theorem radius_small_of_bound {M C r : ℝ} (hM : 0 < M) (hC : 0 < C)
    (hr : r ≤ 1 / (4 * M * C)) : M * C * r ≤ 1 / 4 := by
  have := (le_div_iff₀ (by positivity : 0 < 4 * M * C)).mp hr
  nlinarith

/-- A uniform variation of at most `α/2` preserves a uniform positive
lower bound of `α/2`, with no finiteness assumption on the entry index. -/
theorem positive_entries_of_radius {ι : Type*} (a h : ι → ℝ)
    {α r : ℝ} (ha : ∀ i, α ≤ a i) (hr : r ≤ α / 2)
    (hh : ∀ i, |h i| ≤ r) : ∀ i, α / 2 ≤ a i + h i := by
  intro i
  have := (abs_le.mp (hh i)).1
  have := ha i
  linarith

end PBFStability

namespace PBFStability

open scoped BigOperators

/-- The binomial coefficient comparison used for the quadratic remainder. -/
theorem remainder_choose_bound (d j : ℕ) :
    (d + 2).choose (j + 2) ≤ (d + 2).choose 2 * d.choose j := by
  have h := Nat.choose_mul (n := d + 2) (k := j + 2) (s := 2) (by omega)
  have hp : 1 ≤ (j + 2).choose 2 := Nat.one_le_iff_ne_zero.mpr
    (Nat.choose_ne_zero (by omega))
  calc
    (d + 2).choose (j + 2) ≤ (d + 2).choose (j + 2) * (j + 2).choose 2 := by
      nlinarith
    _ = (d + 2).choose 2 * d.choose j := by simpa using h

/-- The corresponding comparison after differentiating a product term. -/
theorem remainder_derivative_choose_bound (d j : ℕ) :
    (j + 2) * (d + 2).choose (j + 2) ≤ 2 * (d + 2).choose 2 * d.choose j := by
  have h := Nat.choose_mul (n := d + 2) (k := j + 2) (s := 2) (by omega)
  have hj := Nat.choose_mul (n := j + 2) (k := 2) (s := 1) (by omega)
  have hj' : (j + 2).choose 2 * 2 = (j + 2) * (j + 1) := by
    simpa using hj
  have hle : j + 2 ≤ 2 * (j + 2).choose 2 := by nlinarith
  calc
    (j + 2) * (d + 2).choose (j + 2) ≤
        (2 * (j + 2).choose 2) * (d + 2).choose (j + 2) :=
      Nat.mul_le_mul_right _ hle
    _ = 2 * (d + 2).choose 2 * d.choose j := by
      have h' : (d + 2).choose (j + 2) * (j + 2).choose 2 =
          (d + 2).choose 2 * d.choose j := by simpa using h
      nlinarith [h']

/-- `C_p` from the manuscript, with `p = d+2`. -/
def remainderConstant (d : ℕ) (A : ℝ) : ℝ :=
  ((d + 2).choose 2 : ℝ) * (2 + A) ^ d

theorem remainderConstant_eq (d : ℕ) (A : ℝ) :
    remainderConstant d A = ((d + 2 : ℝ) * (d + 1) / 2) * (2 + A) ^ d := by
  have h := Nat.choose_mul (n := d + 2) (k := 2) (s := 1) (by omega)
  have hn : (d + 2).choose 2 * 2 = (d + 2) * (d + 1) := by simpa using h
  have hr : ((d + 2).choose 2 : ℝ) * 2 = (d + 2 : ℝ) * (d + 1) := by
    exact_mod_cast hn
  have hc : ((d + 2).choose 2 : ℝ) = (d + 2 : ℝ) * (d + 1) / 2 := by linarith
  simp only [remainderConstant, hc]

/-- The full quadratic majorant, written with the index `j = k-2`. -/
theorem quadratic_majorant_bound (d : ℕ) {A r : ℝ}
    (hA : 0 ≤ A) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    ∑ j ∈ Finset.range (d + 1), ((d + 2).choose (j + 2) : ℝ) *
      r ^ (j + 2) * (1 + A) ^ (d - j) ≤ remainderConstant d A * r ^ 2 := by
  have hpoint (j : ℕ) : ((d + 2).choose (j + 2) : ℝ) *
      r ^ (j + 2) * (1 + A) ^ (d - j) ≤
      ((d + 2).choose 2 : ℝ) * r ^ 2 *
        ((d.choose j : ℝ) * (1 + A) ^ (d - j)) := by
    have hchoose : ((d + 2).choose (j + 2) : ℝ) ≤
        ((d + 2).choose 2 : ℝ) * (d.choose j : ℝ) := by
      exact_mod_cast remainder_choose_bound d j
    have hpow : r ^ j ≤ 1 := pow_le_one₀ hr hr1
    calc
      _ = ((d + 2).choose (j + 2) : ℝ) * r ^ j * r ^ 2 *
          (1 + A) ^ (d - j) := by rw [pow_add]; ring
      _ ≤ (((d + 2).choose 2 : ℝ) * (d.choose j : ℝ)) * 1 * r ^ 2 *
          (1 + A) ^ (d - j) := by gcongr
      _ = _ := by ring
  have hsum : (∑ j ∈ Finset.range (d + 1),
      (d.choose j : ℝ) * (1 + A) ^ (d - j)) = (2 + A) ^ d := by
    have hp := add_pow (1 : ℝ) (1 + A) d
    simpa only [one_pow, one_mul, show (1 : ℝ) + (1 + A) = 2 + A by ring,
      mul_comm] using hp.symm
  calc
    _ ≤ ∑ j ∈ Finset.range (d + 1), ((d + 2).choose 2 : ℝ) * r ^ 2 *
        ((d.choose j : ℝ) * (1 + A) ^ (d - j)) :=
      Finset.sum_le_sum (fun j _ => hpoint j)
    _ = ((d + 2).choose 2 : ℝ) * r ^ 2 * (2 + A) ^ d := by
      rw [← Finset.mul_sum, hsum]
    _ = remainderConstant d A * r ^ 2 := by unfold remainderConstant; ring

/-- The full Lipschitz majorant for the nonlinear remainder. -/
theorem lipschitz_majorant_bound (d : ℕ) {A r : ℝ}
    (hA : 0 ≤ A) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    ∑ j ∈ Finset.range (d + 1), (j + 2 : ℝ) *
      ((d + 2).choose (j + 2) : ℝ) * r ^ (j + 1) *
      (1 + A) ^ (d - j) ≤ 2 * remainderConstant d A * r := by
  have hpoint (j : ℕ) : (j + 2 : ℝ) * ((d + 2).choose (j + 2) : ℝ) *
      r ^ (j + 1) * (1 + A) ^ (d - j) ≤
      2 * ((d + 2).choose 2 : ℝ) * r *
        ((d.choose j : ℝ) * (1 + A) ^ (d - j)) := by
    have hchoose : (j + 2 : ℝ) * ((d + 2).choose (j + 2) : ℝ) ≤
        2 * ((d + 2).choose 2 : ℝ) * (d.choose j : ℝ) := by
      exact_mod_cast remainder_derivative_choose_bound d j
    have hpow : r ^ j ≤ 1 := pow_le_one₀ hr hr1
    calc
      _ = ((j + 2 : ℝ) * ((d + 2).choose (j + 2) : ℝ)) * r ^ j * r *
          (1 + A) ^ (d - j) := by rw [pow_succ]; ring
      _ ≤ (2 * ((d + 2).choose 2 : ℝ) * (d.choose j : ℝ)) * 1 * r *
          (1 + A) ^ (d - j) := by gcongr
      _ = _ := by ring
  have hsum : (∑ j ∈ Finset.range (d + 1),
      (d.choose j : ℝ) * (1 + A) ^ (d - j)) = (2 + A) ^ d := by
    have hp := add_pow (1 : ℝ) (1 + A) d
    simpa only [one_pow, one_mul, show (1 : ℝ) + (1 + A) = 2 + A by ring,
      mul_comm] using hp.symm
  calc
    _ ≤ ∑ j ∈ Finset.range (d + 1), 2 * ((d + 2).choose 2 : ℝ) * r *
        ((d.choose j : ℝ) * (1 + A) ^ (d - j)) :=
      Finset.sum_le_sum (fun j _ => hpoint j)
    _ = 2 * ((d + 2).choose 2 : ℝ) * r * (2 + A) ^ d := by
      rw [← Finset.mul_sum, hsum]
    _ = 2 * remainderConstant d A * r := by unfold remainderConstant; ring

end PBFStability

namespace PBFStability

variable {B : Type*} [NormedRing B]

/-- The quadratic remainder of multiplying two perturbed factors. No
commutativity assumption is used. -/
def twoFactorRemainder (h : B × B) : B := h.1 * h.2

theorem twoFactor_expansion (a b : B) (h : B × B) :
    (a + h.1) * (b + h.2) = a * b + (h.1 * b + a * h.2) +
      twoFactorRemainder h := by
  simp only [twoFactorRemainder, add_mul, mul_add]
  abel

theorem twoFactor_remainder_bound {r : ℝ} (hr : 0 ≤ r)
    {h : B × B} (hh : ‖h‖ ≤ r) : ‖twoFactorRemainder h‖ ≤ r ^ 2 := by
  have h₁ : ‖h.1‖ ≤ r := (norm_fst_le h).trans hh
  have h₂ : ‖h.2‖ ≤ r := (norm_snd_le h).trans hh
  calc
    ‖twoFactorRemainder h‖ ≤ ‖h.1‖ * ‖h.2‖ := norm_mul_le _ _
    _ ≤ r * r := by gcongr
    _ = r ^ 2 := by ring

theorem twoFactor_remainder_lipschitz {r : ℝ} (hr : 0 ≤ r)
    {h k : B × B} (hh : ‖h‖ ≤ r) (hk : ‖k‖ ≤ r) :
    ‖twoFactorRemainder h - twoFactorRemainder k‖ ≤ 2 * r * ‖h - k‖ := by
  have hh₂ : ‖h.2‖ ≤ r := (norm_snd_le h).trans hh
  have hk₁ : ‖k.1‖ ≤ r := (norm_fst_le k).trans hk
  have hd₁ : ‖h.1 - k.1‖ ≤ ‖h - k‖ := norm_fst_le (h - k)
  have hd₂ : ‖h.2 - k.2‖ ≤ ‖h - k‖ := norm_snd_le (h - k)
  have hid : twoFactorRemainder h - twoFactorRemainder k =
      (h.1 - k.1) * h.2 + k.1 * (h.2 - k.2) := by
    simp only [twoFactorRemainder, sub_mul, mul_sub]
    abel
  calc
    ‖twoFactorRemainder h - twoFactorRemainder k‖
        ≤ ‖(h.1 - k.1) * h.2‖ + ‖k.1 * (h.2 - k.2)‖ := by
          rw [hid]; exact norm_add_le _ _
    _ ≤ ‖h.1 - k.1‖ * ‖h.2‖ + ‖k.1‖ * ‖h.2 - k.2‖ :=
      add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ ‖h - k‖ * r + r * ‖h - k‖ := by gcongr
    _ = 2 * r * ‖h - k‖ := by ring

end PBFStability

#print axioms PBFStability.quantitative_radius
#print axioms PBFStability.quantitative_radius_lipschitz
#print axioms PBFStability.quantitative_radius_solution_bound
#print axioms PBFStability.positive_entries_of_radius
#print axioms PBFStability.quadratic_majorant_bound
#print axioms PBFStability.lipschitz_majorant_bound
#print axioms PBFStability.twoFactor_expansion
#print axioms PBFStability.twoFactor_remainder_bound
#print axioms PBFStability.twoFactor_remainder_lipschitz
