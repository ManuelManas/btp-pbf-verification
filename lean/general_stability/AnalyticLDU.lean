import AnalyticExtraction
import BandSpaces

noncomputable section
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace BTP.GeneralStability

/-- A lower subdiagonal (including d=0) of LDU. The finite sum is
uniform in the row index; zero extension enforces the initial boundary. -/
def lduLowerCoefficient {p q : ℕ} (x : FullBand p q) (d : ℕ) : Seq :=
  ∑ t ∈ Finset.range (q+1), zeroExtension t
    (bandCoefficient x.1 (d+t) * x.2.1 * bandCoefficient x.2.2 t)

/-- An upper subdiagonal of the transposed LDU matrix. -/
def lduUpperCoefficient {p q : ℕ} (x : FullBand p q) (d : ℕ) : Seq :=
  ∑ t ∈ Finset.range (p+1), zeroExtension t
    (bandCoefficient x.1 t * x.2.1 * bandCoefficient x.2.2 (d+t))

/-- The LDU multiplication map in the fixed-band Banach coordinates. -/
def lduProduct {p q : ℕ} (x : FullBand p q) : FullBand p q :=
  (fun r => lduLowerCoefficient x (r.val+1),
    lduLowerCoefficient x 0, fun r => lduUpperCoefficient x (r.val+1))

def lowerProjection (p q : ℕ) : FullBand p q →L[ℝ] LowerBand p :=
  ContinuousLinearMap.fst ℝ (LowerBand p) (Seq × LowerBand q)

def diagonalProjection (p q : ℕ) : FullBand p q →L[ℝ] Seq :=
  (ContinuousLinearMap.fst ℝ Seq (LowerBand q)).comp
    (ContinuousLinearMap.snd ℝ (LowerBand p) (Seq × LowerBand q))

def upperProjection (p q : ℕ) : FullBand p q →L[ℝ] LowerBand q :=
  (ContinuousLinearMap.snd ℝ Seq (LowerBand q)).comp
    (ContinuousLinearMap.snd ℝ (LowerBand p) (Seq × LowerBand q))

theorem analytic_bandCoefficient {p : ℕ} (x : LowerBand p) (d : ℕ) :
    AnalyticAt ℝ (fun y => bandCoefficient y d) x := by
  exact analyticAt_const.add ((strictCoefficientMap p d).analyticAt x)

theorem analytic_lduLowerCoefficient {p q : ℕ} (x : FullBand p q) (d : ℕ) :
    AnalyticAt ℝ (fun y => lduLowerCoefficient y d) x := by
  unfold lduLowerCoefficient
  refine (Finset.range (q+1)).analyticAt_fun_sum ?_
  intro t _
  have hL : AnalyticAt ℝ (fun y : FullBand p q => bandCoefficient y.1 (d+t)) x :=
    (analytic_bandCoefficient x.1 (d+t)).comp
      (f := fun y : FullBand p q => y.1) ((lowerProjection p q).analyticAt x)
  have hD : AnalyticAt ℝ (fun y : FullBand p q => y.2.1) x :=
    (diagonalProjection p q).analyticAt x
  have hU : AnalyticAt ℝ (fun y : FullBand p q => bandCoefficient y.2.2 t) x :=
    (analytic_bandCoefficient x.2.2 t).comp
      (f := fun y : FullBand p q => y.2.2) ((upperProjection p q).analyticAt x)
  exact ((zeroExtension t).analyticAt _).comp (f := fun y : FullBand p q =>
    bandCoefficient y.1 (d+t) * y.2.1 * bandCoefficient y.2.2 t) ((hL.mul hD).mul hU)

theorem analytic_lduUpperCoefficient {p q : ℕ} (x : FullBand p q) (d : ℕ) :
    AnalyticAt ℝ (fun y => lduUpperCoefficient y d) x := by
  unfold lduUpperCoefficient
  refine (Finset.range (p+1)).analyticAt_fun_sum ?_
  intro t _
  have hL : AnalyticAt ℝ (fun y : FullBand p q => bandCoefficient y.1 t) x :=
    (analytic_bandCoefficient x.1 t).comp
      (f := fun y : FullBand p q => y.1) ((lowerProjection p q).analyticAt x)
  have hD : AnalyticAt ℝ (fun y : FullBand p q => y.2.1) x :=
    (diagonalProjection p q).analyticAt x
  have hU : AnalyticAt ℝ (fun y : FullBand p q => bandCoefficient y.2.2 (d+t)) x :=
    (analytic_bandCoefficient x.2.2 (d+t)).comp
      (f := fun y : FullBand p q => y.2.2) ((upperProjection p q).analyticAt x)
  exact ((zeroExtension t).analyticAt _).comp (f := fun y : FullBand p q =>
    bandCoefficient y.1 t * y.2.1 * bandCoefficient y.2.2 (d+t)) ((hL.mul hD).mul hU)

theorem analytic_lduProduct {p q : ℕ} (x : FullBand p q) :
    AnalyticAt ℝ (@lduProduct p q) x := by
  apply AnalyticAt.prod
  · apply AnalyticAt.pi
    intro r
    exact analytic_lduLowerCoefficient x (r.val+1)
  · apply AnalyticAt.prod
    · exact analytic_lduLowerCoefficient x 0
    · apply AnalyticAt.pi
      intro r
      exact analytic_lduUpperCoefficient x (r.val+1)

#print axioms analytic_lduProduct

end BTP.GeneralStability
