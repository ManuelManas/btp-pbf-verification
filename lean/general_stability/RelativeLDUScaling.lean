import RelativeLDUProduct

noncomputable section
open scoped BigOperators
namespace BTP.RelativeStability
open BTP.Stability BTP.GeneralStability

def scaleTriangular {p : ℕ} (l : Fin p → ℕ → ℝ) (R : ℕ → ℝ) : Fin p → ℕ → ℝ :=
  fun i n => l i n*R n/R (n+i.val+1)

def scaleDiagonal (d R S : ℕ → ℝ) : ℕ → ℝ := fun n => d n/(R n*S n)

theorem scaleTriangular_pos {p : ℕ} (l : Fin p → ℕ → ℝ) (R : ℕ → ℝ)
    (hl : ∀ i n,0<l i n) (hR : ∀ n,0<R n) : ∀ i n,0<scaleTriangular l R i n :=
  fun i n => div_pos (mul_pos (hl i n) (hR n)) (hR _)

theorem scaleDiagonal_pos (d R S : ℕ → ℝ) (hd : ∀ n,0<d n)
    (hR : ∀ n,0<R n) (hS : ∀ n,0<S n) : ∀ n,0<scaleDiagonal d R S n :=
  fun n => div_pos (hd n) (mul_pos (hR n) (hS n))

theorem rawTriangular_scale {p : ℕ} (l : Fin p → ℕ → ℝ) (R : ℕ → ℝ)
    (hR : ∀ n,0<R n) (r j : ℕ) :
    rawTriangular (scaleTriangular l R) r j = rawTriangular l r j*R j/R (j+r) := by
  unfold rawTriangular
  split_ifs with hr hp
  · subst r
    simp [ne_of_gt (hR j)]
  · simp only [scaleTriangular]
    congr 1
    congr 1
    omega
  · simp

theorem rawLDUTerm_scale {p q : ℕ} (l : Fin p → ℕ → ℝ) (d : ℕ → ℝ)
    (u : Fin q → ℕ → ℝ) (R S : ℕ → ℝ) (hR : ∀ n,0<R n) (hS : ∀ n,0<S n)
    (r s t j : ℕ) :
    rawLDUTerm (scaleTriangular l R) (scaleDiagonal d R S) (scaleTriangular u S) r s t j =
      rawLDUTerm l d u r s t j/(R (j+r)*S (j+s)) := by
  simp only [rawLDUTerm]
  split_ifs with ht
  · rw [rawTriangular_scale l R hR,rawTriangular_scale u S hS]
    rw [show j-t+(r+t)=j+r by omega,show j-t+(s+t)=j+s by omega]
    simp only [scaleDiagonal]
    field_simp [ne_of_gt (hR (j-t)),ne_of_gt (hS (j-t))]
  · simp

theorem rawLDUSum_scale {p q : ℕ} (l : Fin p → ℕ → ℝ) (d : ℕ → ℝ)
    (u : Fin q → ℕ → ℝ) (R S : ℕ → ℝ) (hR : ∀ n,0<R n) (hS : ∀ n,0<S n)
    (r s N j : ℕ) :
    rawLDUSum (scaleTriangular l R) (scaleDiagonal d R S) (scaleTriangular u S) r s N j =
      rawLDUSum l d u r s N j/(R (j+r)*S (j+s)) := by
  simp only [rawLDUSum,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro t _
  exact rawLDUTerm_scale l d u R S hR hS r s t j

theorem relativeLDUWeight_scale {p q : ℕ} (l : Fin p → ℕ → ℝ) (d : ℕ → ℝ)
    (u : Fin q → ℕ → ℝ) (hl : ∀ i n,0<l i n) (hd : ∀ n,0<d n) (hu : ∀ i n,0<u i n)
    (R S : ℕ → ℝ) (hR : ∀ n,0<R n) (hS : ∀ n,0<S n) (r s N t : ℕ) :
    relativeLDUWeight (scaleTriangular l R) (scaleDiagonal d R S) (scaleTriangular u S)
      (scaleTriangular_pos l R hl hR) (scaleDiagonal_pos d R S hd hR hS)
      (scaleTriangular_pos u S hu hS) r s N t = relativeLDUWeight l d u hl hd hu r s N t := by
  apply BoundedContinuousFunction.ext
  intro j
  by_cases ht : t<N
  · rw [relativeLDUWeight_apply _ _ _ _ _ _ _ _ _ _ _ ht,
      relativeLDUWeight_apply _ _ _ _ _ _ _ _ _ _ _ ht,
      rawLDUTerm_scale l d u R S hR hS,rawLDUSum_scale l d u R S hR hS]
    exact div_div_div_cancel_right₀ (ne_of_gt (mul_pos (hR _) (hS _))) _ _
  · simp [relativeLDUWeight,ofAbsBound,ht]

theorem relativeLDUProduct_scale {p q : ℕ} (l : Fin p → ℕ → ℝ) (d : ℕ → ℝ)
    (u : Fin q → ℕ → ℝ) (hl : ∀ i n,0<l i n) (hd : ∀ n,0<d n) (hu : ∀ i n,0<u i n)
    (R S : ℕ → ℝ) (hR : ∀ n,0<R n) (hS : ∀ n,0<S n) :
    relativeLDUProduct (scaleTriangular l R) (scaleDiagonal d R S) (scaleTriangular u S)
      (scaleTriangular_pos l R hl hR) (scaleDiagonal_pos d R S hd hR hS)
      (scaleTriangular_pos u S hu hS) = relativeLDUProduct l d u hl hd hu := by
  funext x
  simp only [relativeLDUProduct,relativeLDUCoefficient,
    relativeLDUWeight_scale l d u hl hd hu R S hR hS]

theorem relativeLDUProductDerivative_scale {p q : ℕ} (l : Fin p → ℕ → ℝ) (d : ℕ → ℝ)
    (u : Fin q → ℕ → ℝ) (hl : ∀ i n,0<l i n) (hd : ∀ n,0<d n) (hu : ∀ i n,0<u i n)
    (R S : ℕ → ℝ) (hR : ∀ n,0<R n) (hS : ∀ n,0<S n) (x : FullBand p q) :
    relativeLDUProductDerivative (scaleTriangular l R) (scaleDiagonal d R S) (scaleTriangular u S)
      (scaleTriangular_pos l R hl hR) (scaleDiagonal_pos d R S hd hR hS)
      (scaleTriangular_pos u S hu hS) x = relativeLDUProductDerivative l d u hl hd hu x := by
  simp only [relativeLDUProductDerivative,relativeLDUCoefficientDerivative,
    relativeLDUWeight_scale l d u hl hd hu R S hR hS]

#print axioms relativeLDUProduct_scale
#print axioms relativeLDUProductDerivative_scale
end BTP.RelativeStability
