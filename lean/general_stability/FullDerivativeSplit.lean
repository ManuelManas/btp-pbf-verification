import LDUInjectivity

noncomputable section
namespace BTP.GeneralStability

/-- Cancellation of the injective normalized-LDU derivative exposes
bounded right inverses for each triangular factor derivative. -/
theorem block_derivative_right_inverses {p q : ℕ}
    (A B R : FullBand p q →L[ℝ] FullBand p q)
    (L : LowerBand p →L[ℝ] LowerBand p) (U : LowerBand q →L[ℝ] LowerBand q)
    (hB : ∀ v, B v=(L v.1,v.2.1,U v.2.2))
    (hA : Function.Injective A)
    (hR : (A.comp B).comp R=ContinuousLinearMap.id ℝ (FullBand p q)) :
    (∃ S : LowerBand p →L[ℝ] LowerBand p, L.comp S=ContinuousLinearMap.id ℝ (LowerBand p)) ∧
    (∃ S : LowerBand q →L[ℝ] LowerBand q, U.comp S=ContinuousLinearMap.id ℝ (LowerBand q)) := by
  have hcancel (v : FullBand p q) : B (R (A v))=v := by
    apply hA
    exact congrArg (fun C : FullBand p q →L[ℝ] FullBand p q => C (A v)) hR
  let iL : LowerBand p →L[ℝ] FullBand p q :=
    ContinuousLinearMap.inl ℝ (LowerBand p) (Seq × LowerBand q)
  let iU : LowerBand q →L[ℝ] FullBand p q :=
    (ContinuousLinearMap.inr ℝ (LowerBand p) (Seq × LowerBand q)).comp
      (ContinuousLinearMap.inr ℝ Seq (LowerBand q))
  constructor
  · refine ⟨((lowerProjection p q).comp R).comp (A.comp iL),?_⟩
    apply ContinuousLinearMap.ext
    intro E
    change L (R (A (E,0,0))).1=E
    have he := hcancel (E,0,0)
    rw [hB] at he
    exact congrArg Prod.fst he
  · refine ⟨((upperProjection p q).comp R).comp (A.comp iU),?_⟩
    apply ContinuousLinearMap.ext
    intro E
    change U (R (A (0,0,E))).2.2=E
    have he := hcancel (0,0,E)
    rw [hB] at he
    exact congrArg (fun x : FullBand p q => x.2.2) he

#print axioms block_derivative_right_inverses
end BTP.GeneralStability
