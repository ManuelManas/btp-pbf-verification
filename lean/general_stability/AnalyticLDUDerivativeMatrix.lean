import AnalyticLDUMatrix
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp

noncomputable section
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace BTP.GeneralStability

def fullEntryCLM (p q i j : ℕ) : FullBand p q →L[ℝ] ℝ :=
  ({ toFun := fun E => fullEntry E i j
     map_add' := fun E F => fullEntry_add E F i j
     map_smul' := fun c E => fullEntry_smul c E i j } : FullBand p q →ₗ[ℝ] ℝ).mkContinuous 1
      (fun E => by change ‖fullEntry E i j‖ ≤ 1*‖E‖
                   simpa only [Real.norm_eq_abs,one_mul] using fullEntry_abs_le E i j)

@[simp] theorem fullEntryCLM_apply {p q : ℕ} (E : FullBand p q) (i j : ℕ) :
    fullEntryCLM p q i j E = fullEntry E i j := rfl

theorem bandEntry_add_smul {p : ℕ} (a h : LowerBand p) (t : ℝ) (i j : ℕ) :
    bandEntry (a+t•h) i j = bandEntry a i j + t * bandEntry h i j := by
  unfold bandEntry
  split_ifs <;> simp [smul_eq_mul]

theorem unitBandEntry_add_smul {p : ℕ} (a h : LowerBand p) (t : ℝ) (i j : ℕ) :
    unitBandEntry (a+t•h) i j = unitBandEntry a i j + t * bandEntry h i j := by
  by_cases he : i=j
  · subst j
    simp [unitBandEntry,bandEntry]
  · simp only [unitBandEntry,he,↓reduceIte,bandEntry_add_smul]

theorem scalarAffine_hasDerivAt (a b : ℝ) :
    HasDerivAt (fun t : ℝ => a+t*b) b 0 := by
  simpa using ((hasDerivAt_id (0:ℝ)).mul_const b).const_add a

theorem lduProductDerivative_entry_fin {p q N : ℕ} (x E : FullBand p q) (i j : Fin N) :
    fullEntry (lduProductDerivative x E) i.val j.val =
      ∑ k : Fin N,
        (bandEntry E.1 i.val k.val * x.2.1 k.val * unitBandEntry x.2.2 j.val k.val +
         unitBandEntry x.1 i.val k.val * E.2.1 k.val * unitBandEntry x.2.2 j.val k.val +
         unitBandEntry x.1 i.val k.val * x.2.1 k.val * bandEntry E.2.2 j.val k.val) := by
  let f : ℝ → ℝ := fun t => fullEntry (lduProduct (x+t•E)) i.val j.val
  have hline : HasDerivAt (fun t : ℝ => x+t•E) E 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const E).const_add x
  have hleft : HasDerivAt f (fullEntry (lduProductDerivative x E) i.val j.val) 0 := by
    have hd := (fullEntryCLM p q i.val j.val).hasFDerivAt.comp x (lduProduct_hasFDerivAt x)
    have hh := hd.comp_hasDerivAt_of_eq 0 hline (by simp)
    convert hh using 1 <;> rfl
  have hf : f = fun t => ∑ k : Fin N,
      (unitBandEntry x.1 i.val k.val+t*bandEntry E.1 i.val k.val) *
      (x.2.1 k.val+t*E.2.1 k.val) *
      (unitBandEntry x.2.2 j.val k.val+t*bandEntry E.2.2 j.val k.val) := by
    funext t
    dsimp only [f]
    rw [lduProduct_entry_fin]
    apply Finset.sum_congr rfl
    intro k _
    change unitBandEntry (x.1+t•E.1) i.val k.val * (x.2.1+t•E.2.1) k.val *
        unitBandEntry (x.2.2+t•E.2.2) j.val k.val = _
    rw [unitBandEntry_add_smul,unitBandEntry_add_smul]
    rfl
  have hright : HasDerivAt f
      (∑ k : Fin N,
        (bandEntry E.1 i.val k.val * x.2.1 k.val * unitBandEntry x.2.2 j.val k.val +
         unitBandEntry x.1 i.val k.val * E.2.1 k.val * unitBandEntry x.2.2 j.val k.val +
         unitBandEntry x.1 i.val k.val * x.2.1 k.val * bandEntry E.2.2 j.val k.val)) 0 := by
    rw [hf]
    apply HasDerivAt.fun_sum
    intro k _
    have h := ((scalarAffine_hasDerivAt (unitBandEntry x.1 i.val k.val) (bandEntry E.1 i.val k.val)).mul
      (scalarAffine_hasDerivAt (x.2.1 k.val) (E.2.1 k.val))).mul
      (scalarAffine_hasDerivAt (unitBandEntry x.2.2 j.val k.val) (bandEntry E.2.2 j.val k.val))
    convert h using 1 <;> first | rfl | (dsimp; ring)
  exact hleft.unique hright

theorem finiteStrictLower_entry {p q N : ℕ} (E : FullBand p q) (i j : Fin N) :
    BTP.Stability.BandLDU.lowerPart (fullSection E N) i j =
      bandEntry E.1 i.val j.val := by
  by_cases hj : j < i
  · have hne : i.val≠j.val := by omega
    simp [BTP.Stability.BandLDU.lowerPart,hj,fullSection,fullEntry,hne]
  · simp [BTP.Stability.BandLDU.lowerPart,hj,bandEntry,show ¬j.val < i.val from hj]

theorem finiteStrictUpper_entry {p q N : ℕ} (E : FullBand p q) (i j : Fin N) :
    BTP.Stability.BandLDU.upperPart (fullSection E N) i j =
      bandEntry E.2.2 j.val i.val := by
  by_cases hi : i < j
  · have hne : i.val≠j.val := by omega
    simp [BTP.Stability.BandLDU.upperPart,hi,fullSection,fullEntry,hne,
      show ¬j.val < i.val by omega]
  · simp [BTP.Stability.BandLDU.upperPart,hi,bandEntry,show ¬i.val < j.val from hi]

theorem finiteDiag_entry {p q : ℕ} (E : FullBand p q) (N : ℕ) :
    BTP.Stability.BandLDU.diagPart (fullSection E N) =
      Matrix.diagonal (fun i : Fin N => E.2.1 i.val) := by
  simp only [BTP.Stability.BandLDU.diagPart,fullSection,fullEntry_diag]

/-- The derivative used in the analytic inverse theorem agrees exactly,
on every finite leading section, with δL D U + L δD U + L D δU. -/
theorem lduProductDerivative_section {p q : ℕ} (x E : FullBand p q) (N : ℕ) :
    fullSection (lduProductDerivative x E) N =
      BTP.Stability.BandLDU.variation
        (1 + BTP.Stability.BandLDU.lowerPart (fullSection x N))
        (Matrix.diagonal (fun i : Fin N => x.2.1 i.val))
        (1 + BTP.Stability.BandLDU.upperPart (fullSection x N))
        (BTP.Stability.BandLDU.lowerPart (fullSection E N))
        (BTP.Stability.BandLDU.diagPart (fullSection E N))
        (BTP.Stability.BandLDU.upperPart (fullSection E N)) := by
  ext i j
  change fullEntry (lduProductDerivative x E) i.val j.val = _
  rw [lduProductDerivative_entry_fin]
  simp only [BTP.Stability.BandLDU.variation,Matrix.add_apply,finiteDiag_entry]
  simp only [Matrix.mul_apply,finiteStrictLower_entry,
    finiteStrictUpper_entry,finiteLower_entry,finiteUpper_entry]
  simp [Matrix.diagonal,Finset.sum_add_distrib]

#print axioms lduProductDerivative_section

end BTP.GeneralStability
