import FreeQuotientExtraction
import FreeProductDerivative

set_option maxHeartbeats 2000000
noncomputable section
namespace BTP.GeneralStability
open BTP.Stability BTP.FreeScalar

/-- Every scalar factor with an exponential dichotomy has a bounded
linear right inverse which preserves sequences tending to zero. -/
theorem freeFirstOrder_rightInverse (j : ℕ) (a : Seq) (b : ℕ → Seq)
    (α : ℝ) (hα : 0<α) (ha : ∀ n,α≤a n) (hb : ∀ n,α≤b j n)
    (hg : Geometric (fun n => a (n+j+1)/b j n) ∨
      Geometric (fun n => (a (n+j+1)/b j n)⁻¹)) :
    ∃ R : Seq →L[ℝ] Seq, (freeFirstOrder j a b).comp R=ContinuousLinearMap.id ℝ Seq ∧
      PreservesCZero R := by
  let w := translate (j+1) a * positiveReciprocal (b j) α hα hb
  let u := b j * positiveReciprocal (translate (j+1) a) α hα (fun n => ha (n+(j+1)))
  have hw : ∀ n,0<w n := by
    intro n
    change 0<a (n+(j+1))*(1/b j n)
    exact mul_pos (lt_of_lt_of_le hα (ha _)) (one_div_pos.mpr (lt_of_lt_of_le hα (hb n)))
  have hu : ∀ n,0<u n := by
    intro n
    change 0<b j n*(1/a (n+(j+1)))
    exact mul_pos (lt_of_lt_of_le hα (hb n)) (one_div_pos.mpr (lt_of_lt_of_le hα (ha _)))
  have huw : ∀ n,u n*w n=1 := by
    intro n
    change (b j n*(1/a (n+(j+1))))*(a (n+(j+1))*(1/b j n))=1
    have ha' : a (n+(j+1))≠0 := ne_of_gt (lt_of_lt_of_le hα (ha _))
    have hb' : b j n≠0 := ne_of_gt (lt_of_lt_of_le hα (hb n))
    field_simp
  have hew : (w : ℕ → ℝ) = fun n => a (n+j+1)/b j n := by
    funext n
    change a (n+(j+1))*(1/b j n)=_
    rw [Nat.add_assoc]
    ring
  have heu : (u : ℕ → ℝ) = fun n => (a (n+j+1)/b j n)⁻¹ := by
    funext n
    change b j n*(1/a (n+(j+1)))=_
    simp [div_eq_mul_inv,Nat.add_assoc]
  have hgu : Geometric w ∨ Geometric u := by simpa only [hew,heu] using hg
  have hex : ∃ R : Seq →L[ℝ] Seq,
      (freeDifference w).comp R=ContinuousLinearMap.id ℝ Seq ∧ PreservesCZero R := by
    rcases hgu with hf|hr
    · exact freeDifference_forward_rightInverse w (fun n => (hw n).le) hf
    · obtain ⟨R,hR,_,hRc⟩ := freeDifference_reciprocal_rightInverse w u hu huw hr
      exact ⟨R,hR,hRc⟩
  obtain ⟨R,hR,hRc⟩ := hex
  let N : Seq →L[ℝ] Seq := ContinuousLinearMap.mul ℝ Seq
    (translate 1 (positiveReciprocal (b j) α hα hb))
  refine ⟨R.comp N,?_,preservesCZero_comp R N hRc (multiply_preserves_cZero _)⟩
  apply ContinuousLinearMap.ext
  intro f
  rw [freeFirstOrder_normalization j a b α hα hb]
  change diagonalEquiv (translate 1 (b j)) α hα (fun n => hb (n+1))
    (freeDifference w (R (N f))) = f
  have hh := congrArg (fun A : Seq →L[ℝ] Seq => A (N f)) hR
  change freeDifference w (R (N f))=N f at hh
  rw [hh]
  apply BoundedContinuousFunction.ext
  intro n
  change b j (n+1)*((1/b j (n+1))*f n)=f n
  have hn : b j (n+1)≠0 := ne_of_gt (lt_of_lt_of_le hα (hb _))
  field_simp

theorem freeFirstOrderComposition_rightInverse (a : Seq) (b : ℕ → Seq)
    (α : ℝ) (hα : 0<α) (ha : ∀ n,α≤a n) (m : ℕ)
    (hb : ∀ i<m,∀ n,α≤b i n)
    (hg : ∀ i<m,Geometric (fun n => a (n+i+1)/b i n) ∨
      Geometric (fun n => (a (n+i+1)/b i n)⁻¹)) :
    ∃ R : Seq →L[ℝ] Seq,
      (freeFirstOrderComposition a b m).comp R=ContinuousLinearMap.id ℝ Seq ∧
      PreservesCZero R := by
  induction m with
  | zero => exact ⟨ContinuousLinearMap.id ℝ Seq,rfl,fun _ hv => hv⟩
  | succ m ih =>
    obtain ⟨R,hR,hRc⟩ := ih (fun i hi n => hb i (by omega) n) (fun i hi => hg i (by omega))
    obtain ⟨S,hS,hSc⟩ := freeFirstOrder_rightInverse m a b α hα ha (hb m (by omega)) (hg m (by omega))
    refine ⟨R.comp S,?_,preservesCZero_comp R S hRc hSc⟩
    apply ContinuousLinearMap.ext
    intro f
    change freeFirstOrder m a b (freeFirstOrderComposition a b m (R (S f)))=f
    have hr := congrArg (fun A : Seq →L[ℝ] Seq => A (S f)) hR
    change freeFirstOrderComposition a b m (R (S f))=S f at hr
    rw [hr]
    exact congrArg (fun A : Seq →L[ℝ] Seq => A f) hS

theorem eliminationMap_preserves_cZero {w : ℕ} (a : Seq) (E : LowerBand w)
    (hE : ∀ r,E r∈cZero) (s : ℕ) : eliminationMap a w s E∈cZero := by
  induction s with
  | zero => exact cZero.zero_mem
  | succ s ih =>
    change strictCoefficientMap w (s+1) E - translate (s+1) a * eliminationMap a w s E∈cZero
    exact cZero.sub_mem (strictCoefficientMap_preserves_cZero E hE _)
      (sequence_mul_preserves_cZero _ _ ih)

theorem freeResidualMap_preserves_cZero {m : ℕ} (a : Seq) (G : LowerBand m) (s : ℕ) :
    PreservesCZero (freeResidualMap a G s) := by
  intro h hh
  induction s with
  | zero => exact cZero.zero_mem
  | succ s ih =>
    change bandCoefficient G s * translate (s+1) (zeroExtension 1 h) -
      translate (s+1) a * freeResidualMap a G s h∈cZero
    exact cZero.sub_mem (sequence_mul_preserves_cZero _ _
      (translate_preserves_cZero _ _ (zeroExtension_preserves_cZero 1 h hh)))
      (sequence_mul_preserves_cZero _ _ ih)

/-- A bounded scalar right inverse gives a bounded right inverse for
all coefficients of the genuine extraction derivative. -/
theorem freeExtraction_rightInverse_of_scalar {m : ℕ} (a : Seq) (G : LowerBand m)
    (S : Seq →L[ℝ] Seq)
    (hS : (freeResidualMap a G (m+1)).comp S=ContinuousLinearMap.id ℝ Seq)
    (hSc : PreservesCZero S) :
    ∃ R : LowerBand (m+1) →L[ℝ] (Seq × LowerBand m),
      (freeExtractionDerivative a G).comp R=ContinuousLinearMap.id ℝ (LowerBand (m+1)) ∧
      (∀ E,(∀ r,E r∈cZero) → (R E).1∈cZero ∧ ∀ r,(R E).2 r∈cZero) := by
  let H := S.comp (eliminationMap a (m+1) (m+1))
  let V : LowerBand (m+1) →L[ℝ] LowerBand m := ContinuousLinearMap.pi fun r =>
    eliminationMap a (m+1) (r.val+1) - (freeResidualMap a G (r.val+1)).comp H
  refine ⟨H.prod V,?_,?_⟩
  · apply ContinuousLinearMap.ext
    intro E
    change freeExtractionDerivative a G (H E,V E)=E
    have hh := congrArg (fun A : Seq →L[ℝ] Seq => A (eliminationMap a (m+1) (m+1) E)) hS
    exact freeExtraction_solves a G (H E) E hh
  · intro E hE
    have hh : H E∈cZero := hSc _ (eliminationMap_preserves_cZero a E hE (m+1))
    refine ⟨hh,?_⟩
    intro r
    exact cZero.sub_mem (eliminationMap_preserves_cZero a E hE (r.val+1))
      (freeResidualMap_preserves_cZero a G (r.val+1) (H E) hh)

/-- Complete sufficiency for arbitrary-band extraction with variable
initial entries, with a continuous linear right inverse. -/
theorem freeExtraction_rightInverse_of_pairs (m : ℕ) (a : Seq) (b : ℕ → Seq)
    (α : ℝ) (hα : 0<α) (ha : ∀ n,α≤a n) (hb : ∀ i<m,∀ n,α≤b i n)
    (hg : ∀ i<m,Geometric (fun n => a (n+i+1)/b i n) ∨
      Geometric (fun n => (a (n+i+1)/b i n)⁻¹)) :
    ∃ R : LowerBand (m+1) →L[ℝ] (Seq × LowerBand m),
      (freeExtractionDerivative a (finiteProductBand m b)).comp R=
        ContinuousLinearMap.id ℝ (LowerBand (m+1)) ∧
      (∀ E,(∀ r,E r∈cZero) → (R E).1∈cZero ∧ ∀ r,(R E).2 r∈cZero) := by
  obtain ⟨S,hS,hSc⟩ := freeFirstOrderComposition_rightInverse a b α hα ha m hb hg
  apply freeExtraction_rightInverse_of_scalar a (finiteProductBand m b) S
  · simpa only [freeResidualMap_product_eq_composition] using hS
  · exact hSc

#print axioms freeExtraction_rightInverse_of_pairs

end BTP.GeneralStability
