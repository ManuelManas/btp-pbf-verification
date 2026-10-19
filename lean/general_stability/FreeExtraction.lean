import LowerStability
import FreeScalar

/-! Extraction with variable initial entries. The domains of the scalar
first-order factors are shifted successively, as in the manuscript. -/

noncomputable section
namespace BTP.GeneralStability
open BTP.Stability

/-- The derivative of extraction with all subdiagonal entries of the
first factor free, starting at the first actual subdiagonal row. -/
def freeExtractionDerivative {m : ℕ} (a : Seq) (G : LowerBand m) :
    (Seq × LowerBand m) →L[ℝ] LowerBand (m+1) :=
  (leftExtractionDerivative a G).comp
    ((zeroExtension 1).prodMap (ContinuousLinearMap.id ℝ (LowerBand m)))

def freeResidualMap {m : ℕ} (a : Seq) (G : LowerBand m) : ℕ → Seq →L[ℝ] Seq
  | 0 => 0
  | s+1 => bandCoefficient G s • ((translate (s+1)).comp (zeroExtension 1)) -
      translate (s+1) a • freeResidualMap a G s

@[simp] theorem freeResidualMap_zero {m : ℕ} (a : Seq) (G : LowerBand m) :
    freeResidualMap a G 0 = 0 := rfl

theorem freeResidualMap_succ {m : ℕ} (a : Seq) (G : LowerBand m) (s : ℕ) (h : Seq) (j : ℕ) :
    freeResidualMap a G (s+1) h j =
      initialExtension 1 h (j+s+1)*bandCoefficient G s j -
      a (j+s+1)*freeResidualMap a G s h j := by
  simp [freeResidualMap, Nat.add_assoc, mul_comm]

theorem freeExtractionDerivative_coordinate {m : ℕ} (a : Seq) (G : LowerBand m)
    (h : Seq) (R : LowerBand m) (r : Fin (m+1)) (j : ℕ) :
    freeExtractionDerivative a G (h,R) r j =
      strictCoefficientMap m (r.val+1) R j +
      initialExtension 1 h (j+r.val+1)*bandCoefficient G r.val j +
      a (j+r.val+1)*strictCoefficientMap m r.val R j := by
  change leftExtractionDerivative a G (zeroExtension 1 h,R) r j = _
  rw [leftExtractionDerivative_apply, zeroExtension_apply]

theorem elimination_freeExtraction {m : ℕ} (a : Seq) (G : LowerBand m)
    (h : Seq) (R : LowerBand m) (s : ℕ) (hs : s ≤ m+1) :
    eliminationMap a (m+1) s (freeExtractionDerivative a G (h,R)) =
      freeResidualMap a G s h + strictCoefficientMap m s R := by
  induction s with
  | zero => simp
  | succ s ih =>
    have ih' := ih (by omega)
    apply BoundedContinuousFunction.ext
    intro j
    rw [eliminationMap_succ, strictCoefficientMap_coordinate _ ⟨s,by omega⟩,
      freeExtractionDerivative_coordinate, ih']
    change _ = freeResidualMap a G (s+1) h j + strictCoefficientMap m (s+1) R j
    rw [freeResidualMap_succ]
    simp only [BoundedContinuousFunction.add_apply]
    ring

/-- All remaining factor variations are reconstructed from the chosen
first-factor variation by bounded linear operations. -/
def freeExtractionRemainder {m : ℕ} (a : Seq) (G : LowerBand m)
    (h : Seq) (E : LowerBand (m+1)) : LowerBand m :=
  fun r => eliminationMap a (m+1) (r.val+1) E - freeResidualMap a G (r.val+1) h

theorem freeExtraction_solves {m : ℕ} (a : Seq) (G : LowerBand m)
    (h : Seq) (E : LowerBand (m+1))
    (htop : freeResidualMap a G (m+1) h = eliminationMap a (m+1) (m+1) E) :
    freeExtractionDerivative a G (h,freeExtractionRemainder a G h E) = E := by
  let R := freeExtractionRemainder a G h E
  have hR (s : ℕ) (hs : s ≤ m+1) :
      strictCoefficientMap m s R = eliminationMap a (m+1) s E - freeResidualMap a G s h := by
    by_cases hz : s=0
    · subst s; simp
    by_cases hsm : s ≤ m
    · obtain ⟨t,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hz
      exact strictCoefficientMap_coordinate R ⟨t,by omega⟩
    · have he : s=m+1 := by omega
      subst s
      rw [strictCoefficientMap_outside m (m+1) (by omega)]
      simp [htop]
  funext r
  apply BoundedContinuousFunction.ext
  intro j
  rw [freeExtractionDerivative_coordinate, hR (r.val+1) (by omega), hR r.val (by omega)]
  simp only [BoundedContinuousFunction.sub_apply]
  rw [eliminationMap_succ, freeResidualMap_succ]
  rw [strictCoefficientMap_coordinate E r]
  ring

/-- Unlike the fixed-initial problem, uniqueness is not required here.
Surjectivity of the actual matrix derivative is equivalent to that of
its scalar residual. -/
theorem freeExtraction_surjective_iff {m : ℕ} (a : Seq) (G : LowerBand m) :
    Function.Surjective (freeExtractionDerivative a G) ↔
      Function.Surjective (freeResidualMap a G (m+1)) := by
  constructor
  · intro hs f
    obtain ⟨⟨h,R⟩,hx⟩ := hs (deepestBand m f)
    refine ⟨h,?_⟩
    have hh := elimination_freeExtraction a G h R (m+1) (le_refl _)
    rw [hx, elimination_deepest, strictCoefficientMap_outside m (m+1) (by omega)] at hh
    simpa using hh.symm
  · intro hs E
    obtain ⟨h,hh⟩ := hs (eliminationMap a (m+1) (m+1) E)
    exact ⟨(h,freeExtractionRemainder a G h E),freeExtraction_solves a G h E hh⟩

/-- First-order scalar factor between successive shifted sequence
spaces, represented on one common copy of bounded sequences. -/
def freeFirstOrder (j : ℕ) (a : Seq) (b : ℕ → Seq) : Seq →L[ℝ] Seq :=
  (translate 1 (b j)) • translate 1 - (translate (j+2) a) • ContinuousLinearMap.id ℝ Seq

@[simp] theorem freeFirstOrder_apply (j : ℕ) (a : Seq) (b : ℕ → Seq) (h : Seq) (n : ℕ) :
    freeFirstOrder j a b h n = b j (n+1)*h (n+1)-a (n+j+2)*h n := by
  simp [freeFirstOrder, Nat.add_assoc]

def freeFirstOrderComposition (a : Seq) (b : ℕ → Seq) : ℕ → Seq →L[ℝ] Seq
  | 0 => ContinuousLinearMap.id ℝ Seq
  | j+1 => (freeFirstOrder j a b).comp (freeFirstOrderComposition a b j)

/-- The shifted-domain composition is exactly the scalar product from
matrix elimination; no condition is placed on the initial value. -/
theorem freeFirstOrderComposition_apply (a : Seq) (b : ℕ → Seq) (h : Seq) (j n : ℕ) :
    freeFirstOrderComposition a b j h n =
      firstOrderProduct a (fun i n => b i n) (initialExtension 1 h) j (n+j+1) := by
  induction j generalizing n with
  | zero => simp [freeFirstOrderComposition, firstOrderProduct, initialExtension]
  | succ j ih =>
    change freeFirstOrder j a b (freeFirstOrderComposition a b j h) n = _
    rw [freeFirstOrder_apply, ih, ih]
    simp only [firstOrderProduct]
    rw [show n+(j+1)+1-(j+1)=n+1 by omega, show n+(j+1)+1-1=n+j+1 by omega]
    simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem freeResidualMap_product_raw (m : ℕ) (a : Seq) (b : ℕ → Seq) (h : Seq) (s j : ℕ) :
    freeResidualMap a (finiteProductBand m b) s h j =
      eliminate a (leftVariation (initialExtension 1 h)
        (productCoefficients (fun i n => b i n) m)) s (j+s) := by
  induction s with
  | zero => rfl
  | succ s ih =>
    rw [freeResidualMap_succ, bandCoefficient_finiteProduct, ih]
    simp only [eliminate, leftVariation]
    rw [show j+(s+1)-1=j+s by omega, show j+(s+1)=j+s+1 by omega]

/-- The eliminated scalar equation for the actual derivative is the
successive composition on shifted domains. -/
theorem freeResidualMap_product_eq_composition (m : ℕ) (a : Seq) (b : ℕ → Seq) :
    freeResidualMap a (finiteProductBand m b) (m+1) =
      freeFirstOrderComposition a b m := by
  apply ContinuousLinearMap.ext
  intro h
  apply BoundedContinuousFunction.ext
  intro j
  rw [freeResidualMap_product_raw, freeFirstOrderComposition_apply]
  change scalarResidual a (initialExtension 1 h)
      (productCoefficients (fun i n => b i n) m) m (j+(m+1)) = _
  rw [scalarResidual_eq_firstOrderProduct, Nat.add_assoc]

/-- Normalization by the positive diagonal identifies a free first-order
factor with the scalar free-initial-value difference operator. -/
theorem freeFirstOrder_normalization (j : ℕ) (a : Seq) (b : ℕ → Seq)
    (α : ℝ) (hα : 0<α) (hb : ∀ n,α≤b j n) :
    freeFirstOrder j a b =
      (diagonalEquiv (translate 1 (b j)) α hα (fun n => hb (n+1))).toContinuousLinearMap.comp
        (BTP.FreeScalar.freeDifference (translate (j+1) a * positiveReciprocal (b j) α hα hb)) := by
  apply ContinuousLinearMap.ext
  intro h
  apply BoundedContinuousFunction.ext
  intro n
  rw [freeFirstOrder_apply]
  change b j (n+1) * h (n+1) - a (n+j+2) * h n =
    b j (n+1) * (h (n+1) - (a (n+1+(j+1)) * (1 / b j (n+1))) * h n)
  have hn : b j (n+1)≠0 := ne_of_gt (lt_of_lt_of_le hα (hb _))
  rw [show n+1+(j+1)=n+j+2 by omega]
  field_simp

#print axioms freeExtraction_surjective_iff
#print axioms freeResidualMap_product_eq_composition
#print axioms freeFirstOrder_normalization

end BTP.GeneralStability
