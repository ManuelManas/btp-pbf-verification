import LowerStability
import AnalyticInduction
import FreeScalar

/-! The general lower-band criterion, expressed in the actual Banach
spaces of factor entries and matrix subdiagonals. -/

noncomputable section
namespace BTP.GeneralStability
open BTP.Stability

/-- Uniform geometric decay of every consecutive product. -/
def GeometricDecay (w : ℕ → ℝ) : Prop :=
  ∃ C ρ : ℝ, 1≤C ∧ 0<ρ ∧ ρ<1 ∧ ∀ s N, blockProduct w s N≤C*ρ^N

/-- Pair ratios with precisely the shifts induced by the fixed initial
rows. Indices i,j number the actual bidiagonal factors from zero. -/
def pairRatio {p : ℕ} (a : Fin p → Seq) (i j : Fin p) (n : ℕ) : ℝ :=
  a i (n+(p-i.val))/a j (n+(p-j.val))

def PairGeometric (p : ℕ) (a : Fin p → Seq) : Prop :=
  ∀ i j : Fin p, i<j → GeometricDecay (pairRatio a i j)

/-- The adjacent ratios alone suffice; the other pairs telescope. -/
def AdjacentGeometric (p : ℕ) (a : Fin p → Seq) : Prop :=
  ∀ (i : ℕ) (hi : i+1<p),
    GeometricDecay (pairRatio a ⟨i,by omega⟩ ⟨i+1,hi⟩)

/-- Extend a finite family only to express its already-defined matrix
product using the natural-number family of extraction factors. -/
def extendFactors {p : ℕ} (a : Fin p → Seq) (k : ℕ) : Seq :=
  if h : k<p then a ⟨k,h⟩ else 0

@[simp] theorem extendFactors_apply {p : ℕ} (a : Fin p → Seq) (i : Fin p) :
    extendFactors a i.val = a i := by simp [extendFactors, i.isLt]

@[simp] theorem finiteProductBand_extend {p : ℕ} (a : Fin p → Seq) :
    finiteProductBand p (extendFactors a) = lowerProductBand a := by
  unfold finiteProductBand
  congr 1
  funext i
  exact extendFactors_apply a i

theorem GeometricDecay.mul {w v : ℕ → ℝ} (_hw : ∀ n,0≤w n) (hv : ∀ n,0≤v n)
    (hgw : GeometricDecay w) (hgv : GeometricDecay v) :
    GeometricDecay (fun n => w n*v n) := by
  rcases hgw with ⟨C,ρ,hC,hρ,hρ1,hwp⟩
  rcases hgv with ⟨D,τ,hD,hτ,hτ1,hvp⟩
  refine ⟨C*D,ρ*τ,by nlinarith [mul_nonneg (sub_nonneg.mpr hC) (sub_nonneg.mpr hD)],mul_pos hρ hτ,?_,?_⟩
  · nlinarith [mul_pos (sub_pos.mpr hρ1) (sub_pos.mpr hτ1)]
  · intro s N
    have he : blockProduct (fun n => w n*v n) s N = blockProduct w s N*blockProduct v s N := by
      simp [blockProduct, Finset.prod_mul_distrib]
    rw [he]
    calc
      _ ≤ (C*ρ^N)*(D*τ^N) := mul_le_mul (hwp s N) (hvp s N)
        (blockProduct_nonneg hv s N) (mul_nonneg (le_trans zero_le_one hC) (pow_nonneg hρ.le N))
      _ = C*D*(ρ*τ)^N := by rw [mul_pow]; ring

theorem pairRatio_nonneg {p : ℕ} (a : Fin p → Seq) (ha : ∀ i n,0<a i n)
    (i j : Fin p) (n : ℕ) : 0≤pairRatio a i j n :=
  div_nonneg (ha i _).le (ha j _).le

theorem pairRatio_telescopes {p : ℕ} (a : Fin p → Seq) (ha : ∀ i n,0<a i n)
    (i j k : Fin p) :
    pairRatio a i k = fun n => pairRatio a i j n*pairRatio a j k n := by
  funext n
  unfold pairRatio
  have hj : a j (n+(p-j.val)) ≠ 0 := ne_of_gt (ha j _)
  field_simp

theorem pairGeometric_iff_adjacent {p : ℕ} (a : Fin p → Seq) (ha : ∀ i n,0<a i n) :
    PairGeometric p a ↔ AdjacentGeometric p a := by
  constructor
  · intro h i hi
    exact h ⟨i,by omega⟩ ⟨i+1,hi⟩ (by simp)
  · intro h
    have hall (j : ℕ) (hj : j<p) : ∀ (i : ℕ) (hi : i<j),
        GeometricDecay (pairRatio a ⟨i,by omega⟩ ⟨j,hj⟩) := by
      induction j with
      | zero => intro i hi; omega
      | succ j ih =>
        intro i hi
        by_cases he : i=j
        · subst i
          exact h j hj
        · have hij : i<j := by omega
          have hprev := ih (by omega) i hij
          have hlast := h j hj
          rw [pairRatio_telescopes a ha ⟨i,by omega⟩ ⟨j,by omega⟩ ⟨j+1,hj⟩]
          exact GeometricDecay.mul (pairRatio_nonneg a ha _ _) (pairRatio_nonneg a ha _ _) hprev hlast
    intro i j hij
    exact hall j.val j.isLt i.val hij

theorem pairGeometric_succ_iff (p : ℕ) (a : Fin (p+1) → Seq) :
    PairGeometric (p+1) a ↔
      (∀ j : Fin p, GeometricDecay (pairRatio a 0 j.succ)) ∧
      PairGeometric p (Fin.tail a) := by
  have htail (i j : Fin p) : pairRatio a i.succ j.succ = pairRatio (Fin.tail a) i j := by
    funext n
    simp [pairRatio, Fin.tail, Nat.add_sub_add_right]
  constructor
  · intro h
    refine ⟨fun j => h 0 j.succ (by simp),?_⟩
    intro i j hij
    rw [←htail]
    exact h i.succ j.succ (by simpa using hij)
  · rintro ⟨hfirst,ht⟩ i j hij
    revert hij
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j
      · intro hh; exact False.elim (lt_irrefl _ hh)
      · intro _; exact hfirst j
    · refine Fin.cases ?_ (fun j => ?_) j
      · intro hh; simp at hh
      · intro hh
        rw [htail]
        exact ht i j (by simpa using hh)

/-- The geometric conditions contributed by the first bidiagonal factor
are exactly its pair ratios with the remaining factors. -/
theorem firstExtraction_bijective_iff (p : ℕ) (a : Fin (p+1) → Seq)
    (α : ℝ) (hα : 0<α) (ha : ∀ i n,α≤a i n) :
    Function.Bijective (fixedExtractionDerivative (a 0) (lowerProductBand (Fin.tail a))) ↔
      ∀ j : Fin p, GeometricDecay (pairRatio a 0 j.succ) := by
  rw [←finiteProductBand_extend (Fin.tail a)]
  have hb (i : ℕ) (hi : i<p) (n : ℕ) : α≤extendFactors (Fin.tail a) i n := by
    simpa [extendFactors,hi,Fin.tail] using ha (⟨i,hi⟩ : Fin p).succ n
  rw [lower_extraction_bijective_iff p (a 0) (extendFactors (Fin.tail a))
    (fun n => le_trans hα.le (ha 0 n)) α hα hb]
  have hr (j : Fin p) : pairRatio a 0 j.succ =
      fun n => a 0 (n+(p+1))/a j.succ (n+(p-j.val)) := by
    funext n
    simp [pairRatio,Nat.add_sub_add_right]
  constructor
  · intro h j
    rw [hr]
    have hh := h j.val j.isLt
    simpa [GeometricDecay,pairRatio,extendFactors,j.isLt,Fin.tail,Nat.add_sub_add_right,Nat.add_assoc] using hh
  · intro h i hi
    have hh := h ⟨i,hi⟩
    rw [hr] at hh
    simpa [GeometricDecay,pairRatio,extendFactors,hi,Fin.tail,Nat.add_sub_add_right,Nat.add_assoc] using hh

theorem firstExtraction_injective (p : ℕ) (a : Fin (p+1) → Seq)
    (ha : ∀ i n,a i n≠0) :
    Function.Injective (fixedExtractionDerivative (a 0) (lowerProductBand (Fin.tail a))) := by
  rw [←finiteProductBand_extend (Fin.tail a)]
  apply lower_extraction_injective
  intro i hi n
  simpa [extendFactors,hi,Fin.tail] using ha (⟨i,hi⟩ : Fin p).succ n

#print axioms firstExtraction_bijective_iff
#print axioms firstExtraction_injective

/-- Rowwise uniqueness of the derivative for every lower bandwidth.
This is proved from the actual recursive multiplication derivative. -/
theorem fixedProductDerivative_injective (p : ℕ) (a : Fin p → Seq)
    (ha : ∀ i n,a i n≠0) : Function.Injective (fixedProductDerivative p a) := by
  induction p with
  | zero => exact (fixedProductDerivative_zero_bijective a).1
  | succ p ih =>
    exact fixedProductDerivative_succ_injective a (firstExtraction_injective p a ha)
      (ih (Fin.tail a) (fun i n => ha i.succ n))

/-- Complete arbitrary lower-band derivative criterion. No matrix inverse,
elimination equivalence, or positivity conclusion is assumed. -/
theorem fixedProductDerivative_bijective_iff_pairs (p : ℕ) (a : Fin p → Seq)
    (α : ℝ) (hα : 0<α) (ha : ∀ i n,α≤a i n) :
    Function.Bijective (fixedProductDerivative p a) ↔ PairGeometric p a := by
  induction p with
  | zero =>
    constructor
    · intro _ i; exact Fin.elim0 i
    · intro _; exact fixedProductDerivative_zero_bijective a
  | succ p ih =>
    have hne : ∀ i n,a i n≠0 := fun i n => ne_of_gt (lt_of_lt_of_le hα (ha i n))
    rw [fixedProductDerivative_succ_bijective_iff a (firstExtraction_injective p a hne),
      firstExtraction_bijective_iff p a α hα ha,
      ih (Fin.tail a) (fun i n => ha i.succ n), pairGeometric_succ_iff]

/-- The derivative of the genuine fixed-initial product map is a Banach
space isomorphism exactly when every adjacent factor ratio has uniformly
geometrically decaying consecutive products. -/
theorem fixedProductDerivative_bijective_iff_adjacent (p : ℕ) (a : Fin p → Seq)
    (α : ℝ) (hα : 0<α) (ha : ∀ i n,α≤a i n) :
    Function.Bijective (fixedProductDerivative p a) ↔ AdjacentGeometric p a := by
  rw [fixedProductDerivative_bijective_iff_pairs p a α hα ha,
    pairGeometric_iff_adjacent a (fun i n => lt_of_lt_of_le hα (ha i n))]

#print axioms fixedProductDerivative_injective
#print axioms fixedProductDerivative_bijective_iff_pairs
#print axioms fixedProductDerivative_bijective_iff_adjacent

/-- Removing or adjoining finitely many initial weights leaves the
uniform geometric condition unchanged. -/
theorem GeometricDecay.shift_iff {w : ℕ → ℝ} (hw : ∀ n,0≤w n) (r : ℕ) :
    GeometricDecay (fun n => w (r+n)) ↔ GeometricDecay w := by
  constructor
  · exact BTP.FreeScalar.geometric_of_shift hw r
  · rintro ⟨C,ρ,hC,hρ,hρ1,hb⟩
    refine ⟨C,ρ,hC,hρ,hρ1,?_⟩
    intro s N
    rw [BTP.FreeScalar.blockProduct_shift]
    exact hb (r+s) N

/-- The adjacent ratios in the manuscript: consecutive products begin
at row two, so the unused row-zero entries do not enter this condition. -/
def ManuscriptAdjacentGeometric (p : ℕ) (a : Fin p → Seq) : Prop :=
  ∀ (i : ℕ) (hi : i+1<p), GeometricDecay
    (fun n => a ⟨i,by omega⟩ (n+1) / a ⟨i+1,hi⟩ n)

theorem adjacentGeometric_iff_manuscript (p : ℕ) (a : Fin p → Seq)
    (ha : ∀ i n,0<a i n) :
    AdjacentGeometric p a ↔ ManuscriptAdjacentGeometric p a := by
  have hweight (i : ℕ) (hi : i+1<p) :
      pairRatio a ⟨i,by omega⟩ ⟨i+1,hi⟩ =
      fun n => a ⟨i,by omega⟩ (p-i-1+n+1) / a ⟨i+1,hi⟩ (p-i-1+n) := by
    funext n
    unfold pairRatio
    dsimp only
    congr 2 <;> omega
  constructor
  · intro h i hi
    have hg := h i hi
    rw [hweight i hi] at hg
    exact (GeometricDecay.shift_iff
      (fun n => div_nonneg (ha ⟨i,by omega⟩ (n+1)).le (ha ⟨i+1,hi⟩ n).le)
      (p-i-1)).mp hg
  · intro h i hi
    rw [hweight i hi]
    exact (GeometricDecay.shift_iff
      (fun n => div_nonneg (ha ⟨i,by omega⟩ (n+1)).le (ha ⟨i+1,hi⟩ n).le)
      (p-i-1)).mpr (h i hi)

/-- The complete lower-band derivative criterion with exactly the
adjacent weights and initial row conventions of the manuscript. -/
theorem fixedProductDerivative_bijective_iff_manuscript (p : ℕ) (a : Fin p → Seq)
    (α : ℝ) (hα : 0<α) (ha : ∀ i n,α≤a i n) :
    Function.Bijective (fixedProductDerivative p a) ↔ ManuscriptAdjacentGeometric p a := by
  rw [fixedProductDerivative_bijective_iff_adjacent p a α hα ha,
    adjacentGeometric_iff_manuscript p a (fun i n => lt_of_lt_of_le hα (ha i n))]

#print axioms fixedProductDerivative_bijective_iff_manuscript

#print axioms pairGeometric_iff_adjacent
#print axioms pairGeometric_succ_iff

end BTP.GeneralStability
