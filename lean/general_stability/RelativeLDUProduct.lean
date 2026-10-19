import AnalyticLDUDerivative
import RelativeProduct

/-! Genuine normalized LDU multiplication for arbitrary positive raw
entries. No boundedness of the base entries is used. -/
noncomputable section
open Finset
open scoped Topology BigOperators
namespace BTP.RelativeStability
open BTP.Stability BTP.GeneralStability

@[simp] theorem seq_one_apply (n : ℕ) : (1 : Seq) n=1 := rfl

def rawTriangular {p : ℕ} (l : Fin p → ℕ → ℝ) (r j : ℕ) : ℝ :=
  if hr : r=0 then 1 else if h : r≤p then l ⟨r-1,by omega⟩ j else 0

theorem rawTriangular_nonneg {p : ℕ} (l : Fin p → ℕ → ℝ)
    (hl : ∀ i j,0<l i j) (r j : ℕ) : 0≤rawTriangular l r j := by
  unfold rawTriangular
  split_ifs <;> first | positivity | exact (hl _ _).le

theorem rawTriangular_pos {p : ℕ} (l : Fin p → ℕ → ℝ)
    (hl : ∀ i j,0<l i j) (r j : ℕ) (hr : r≤p) : 0<rawTriangular l r j := by
  unfold rawTriangular
  split_ifs <;> first | positivity | exact hl _ _

def rawLDUTerm {p q : ℕ} (l : Fin p → ℕ → ℝ) (d : ℕ → ℝ)
    (u : Fin q → ℕ → ℝ) (r s t j : ℕ) : ℝ :=
  if t≤j then rawTriangular l (r+t) (j-t)*d (j-t)*rawTriangular u (s+t) (j-t) else 0

def rawLDUSum {p q : ℕ} (l : Fin p → ℕ → ℝ) (d : ℕ → ℝ)
    (u : Fin q → ℕ → ℝ) (r s N j : ℕ) : ℝ :=
  ∑ t ∈ range N,rawLDUTerm l d u r s t j

theorem rawLDUTerm_nonneg {p q : ℕ} (l : Fin p → ℕ → ℝ) (d : ℕ → ℝ)
    (u : Fin q → ℕ → ℝ) (hl : ∀ i j,0<l i j) (hd : ∀ j,0<d j)
    (hu : ∀ i j,0<u i j) (r s t j : ℕ) : 0≤rawLDUTerm l d u r s t j := by
  unfold rawLDUTerm
  split_ifs
  · exact mul_nonneg (mul_nonneg (rawTriangular_nonneg l hl _ _) (hd _).le)
      (rawTriangular_nonneg u hu _ _)
  · rfl

theorem rawLDUSum_pos {p q : ℕ} (l : Fin p → ℕ → ℝ) (d : ℕ → ℝ)
    (u : Fin q → ℕ → ℝ) (hl : ∀ i j,0<l i j) (hd : ∀ j,0<d j)
    (hu : ∀ i j,0<u i j) (r s N j : ℕ) (hr : r≤p) (hs : s≤q) (hN : 0<N) :
    0<rawLDUSum l d u r s N j := by
  apply lt_of_lt_of_le (b := rawLDUTerm l d u r s 0 j)
  · simp only [rawLDUTerm,Nat.zero_le,↓reduceIte,Nat.add_zero,Nat.sub_zero]
    exact mul_pos (mul_pos (rawTriangular_pos l hl r j hr) (hd j))
      (rawTriangular_pos u hu s j hs)
  · exact single_le_sum (fun t _ => rawLDUTerm_nonneg l d u hl hd hu r s t j)
      (mem_range.mpr hN)

def relativeLDUWeight {p q : ℕ} (l : Fin p → ℕ → ℝ) (d : ℕ → ℝ)
    (u : Fin q → ℕ → ℝ) (hl : ∀ i j,0<l i j) (hd : ∀ j,0<d j)
    (hu : ∀ i j,0<u i j) (r s N t : ℕ) : Seq :=
  ofAbsBound (fun j => if t<N then rawLDUTerm l d u r s t j/rawLDUSum l d u r s N j else 0) 1 (by
    intro j
    split_ifs with ht
    · have hn := rawLDUTerm_nonneg l d u hl hd hu r s t j
      have hsum : 0≤rawLDUSum l d u r s N j :=
        sum_nonneg fun t _ => rawLDUTerm_nonneg l d u hl hd hu r s t j
      have hle : rawLDUTerm l d u r s t j≤rawLDUSum l d u r s N j :=
        single_le_sum (fun t _ => rawLDUTerm_nonneg l d u hl hd hu r s t j) (mem_range.mpr ht)
      rw [abs_of_nonneg (div_nonneg hn hsum)]
      by_cases hz : rawLDUSum l d u r s N j=0
      · simp [hz]
      · exact (div_le_one (lt_of_le_of_ne hsum (Ne.symm hz))).mpr hle
    · simp)

theorem relativeLDUWeight_apply {p q : ℕ} (l : Fin p → ℕ → ℝ) (d : ℕ → ℝ)
    (u : Fin q → ℕ → ℝ) (hl : ∀ i j,0<l i j) (hd : ∀ j,0<d j)
    (hu : ∀ i j,0<u i j) (r s N t j : ℕ) (ht : t<N) :
    relativeLDUWeight l d u hl hd hu r s N t j=rawLDUTerm l d u r s t j/rawLDUSum l d u r s N j := by
  simp [relativeLDUWeight,ofAbsBound,ht]

def relativeLDUTerm {p q : ℕ} (x : FullBand p q) (r s t : ℕ) : Seq :=
  zeroExtension t ((1+strictCoefficientMap p r x.1)*(1+x.2.1)*(1+strictCoefficientMap q s x.2.2))

def relativeLDUCoefficient {p q : ℕ} (l : Fin p → ℕ → ℝ) (d : ℕ → ℝ)
    (u : Fin q → ℕ → ℝ) (hl : ∀ i j,0<l i j) (hd : ∀ j,0<d j)
    (hu : ∀ i j,0<u i j) (r s N : ℕ) (x : FullBand p q) : Seq :=
  (∑ t ∈ range N, relativeLDUWeight l d u hl hd hu r s N t * relativeLDUTerm x (r+t) (s+t) t)-1

def relativeLDUProduct {p q : ℕ} (l : Fin p → ℕ → ℝ) (d : ℕ → ℝ)
    (u : Fin q → ℕ → ℝ) (hl : ∀ i j,0<l i j) (hd : ∀ j,0<d j)
    (hu : ∀ i j,0<u i j) (x : FullBand p q) : FullBand p q :=
  (fun r => relativeLDUCoefficient l d u hl hd hu (r.val+1) 0 (q+1) x,
    relativeLDUCoefficient l d u hl hd hu 0 0 (q+1) x,
    fun s => relativeLDUCoefficient l d u hl hd hu 0 (s.val+1) (p+1) x)

theorem analytic_relativeLDUTerm {p q : ℕ} (x : FullBand p q) (r s t : ℕ) :
    AnalyticAt ℝ (fun y => relativeLDUTerm y r s t) x := by
  have hL := (analyticAt_const (v := (1 : Seq))).add (((strictCoefficientMap p r).comp (lowerProjection p q)).analyticAt x)
  have hD := (analyticAt_const (v := (1 : Seq))).add ((diagonalProjection p q).analyticAt x)
  have hU := (analyticAt_const (v := (1 : Seq))).add (((strictCoefficientMap q s).comp (upperProjection p q)).analyticAt x)
  exact ((zeroExtension t).analyticAt _).comp ((hL.mul hD).mul hU)

theorem analytic_relativeLDUCoefficient {p q : ℕ} (l : Fin p → ℕ → ℝ) (d : ℕ → ℝ)
    (u : Fin q → ℕ → ℝ) (hl : ∀ i j,0<l i j) (hd : ∀ j,0<d j)
    (hu : ∀ i j,0<u i j) (r s N : ℕ) (x : FullBand p q) :
    AnalyticAt ℝ (relativeLDUCoefficient l d u hl hd hu r s N) x := by
  apply AnalyticAt.sub _ analyticAt_const
  apply (range N).analyticAt_fun_sum
  intro t _
  exact analyticAt_const.mul (analytic_relativeLDUTerm x (r+t) (s+t) t)

theorem analytic_relativeLDUProduct {p q : ℕ} (l : Fin p → ℕ → ℝ) (d : ℕ → ℝ)
    (u : Fin q → ℕ → ℝ) (hl : ∀ i j,0<l i j) (hd : ∀ j,0<d j)
    (hu : ∀ i j,0<u i j) (x : FullBand p q) :
    AnalyticAt ℝ (relativeLDUProduct l d u hl hd hu) x := by
  apply AnalyticAt.prod
  · exact AnalyticAt.pi fun r => analytic_relativeLDUCoefficient l d u hl hd hu _ _ _ x
  · exact AnalyticAt.prod (analytic_relativeLDUCoefficient l d u hl hd hu 0 0 (q+1) x)
      (AnalyticAt.pi fun s => analytic_relativeLDUCoefficient l d u hl hd hu _ _ _ x)

theorem rawTriangular_perturbed {p : ℕ} (l : Fin p → ℕ → ℝ) (x : LowerBand p)
    (r j : ℕ) :
    rawTriangular (fun i n => l i n*(1+x i n)) r j =
      rawTriangular l r j*(1+strictCoefficientMap p r x j) := by
  unfold rawTriangular strictCoefficientMap
  split_ifs <;> simp_all
  omega

theorem rawLDUTerm_perturbed {p q : ℕ} (l : Fin p → ℕ → ℝ) (d : ℕ → ℝ)
    (u : Fin q → ℕ → ℝ) (x : FullBand p q) (r s t j : ℕ) :
    rawLDUTerm (fun i n => l i n*(1+x.1 i n)) (fun n => d n*(1+x.2.1 n))
      (fun i n => u i n*(1+x.2.2 i n)) r s t j =
      rawLDUTerm l d u r s t j * relativeLDUTerm x (r+t) (s+t) t j := by
  simp only [rawLDUTerm,relativeLDUTerm,zeroExtension_apply,initialExtension]
  split_ifs with ht
  · rw [rawTriangular_perturbed,rawTriangular_perturbed]
    simp only [BoundedContinuousFunction.mul_apply,BoundedContinuousFunction.add_apply,
      seq_one_apply]
    ring
  · simp

theorem relativeLDUCoefficient_actual {p q : ℕ} (l : Fin p → ℕ → ℝ) (d : ℕ → ℝ)
    (u : Fin q → ℕ → ℝ) (hl : ∀ i j,0<l i j) (hd : ∀ j,0<d j)
    (hu : ∀ i j,0<u i j) (r s N : ℕ) (hr : r≤p) (hs : s≤q) (hN : 0<N)
    (x : FullBand p q) (j : ℕ) :
    relativeLDUCoefficient l d u hl hd hu r s N x j =
      (rawLDUSum (fun i n => l i n*(1+x.1 i n)) (fun n => d n*(1+x.2.1 n))
        (fun i n => u i n*(1+x.2.2 i n)) r s N j - rawLDUSum l d u r s N j)/
        rawLDUSum l d u r s N j := by
  have hne := ne_of_gt (rawLDUSum_pos l d u hl hd hu r s N j hr hs hN)
  simp only [relativeLDUCoefficient,BoundedContinuousFunction.sub_apply,
    BoundedContinuousFunction.sum_apply,BoundedContinuousFunction.mul_apply,
    seq_one_apply]
  have he : (∑ t ∈ range N,
      relativeLDUWeight l d u hl hd hu r s N t j * relativeLDUTerm x (r+t) (s+t) t j) =
      rawLDUSum (fun i n => l i n*(1+x.1 i n)) (fun n => d n*(1+x.2.1 n))
        (fun i n => u i n*(1+x.2.2 i n)) r s N j/rawLDUSum l d u r s N j := by
    rw [rawLDUSum,Finset.sum_div]
    apply sum_congr rfl
    intro t ht
    rw [relativeLDUWeight_apply l d u hl hd hu r s N t j (mem_range.mp ht),
      rawLDUTerm_perturbed]
    ring
  rw [he]
  field_simp

@[simp] theorem relativeLDUProduct_zero {p q : ℕ} (l : Fin p → ℕ → ℝ) (d : ℕ → ℝ)
    (u : Fin q → ℕ → ℝ) (hl : ∀ i j,0<l i j) (hd : ∀ j,0<d j)
    (hu : ∀ i j,0<u i j) : relativeLDUProduct l d u hl hd hu 0=0 := by
  have he (r s N : ℕ) (hr : r≤p) (hs : s≤q) (hN : 0<N) :
      relativeLDUCoefficient l d u hl hd hu r s N (0 : FullBand p q)=0 := by
    apply BoundedContinuousFunction.ext
    intro j
    rw [relativeLDUCoefficient_actual l d u hl hd hu r s N hr hs hN]
    simp
  apply Prod.ext
  · funext r
    exact he (r.val+1) 0 (q+1) (by omega) (by omega) (by omega)
  · apply Prod.ext
    · exact he 0 0 (q+1) (by omega) (by omega) (by omega)
    · funext s
      exact he 0 (s.val+1) (p+1) (by omega) (by omega) (by omega)

def relativeLDUTermDerivative {p q : ℕ} (x : FullBand p q) (r s t : ℕ) :
    FullBand p q →L[ℝ] Seq :=
  (zeroExtension t).comp
    (((1+strictCoefficientMap p r x.1)*(1+x.2.1)) •
        ((strictCoefficientMap q s).comp (upperProjection p q)) +
      (1+strictCoefficientMap q s x.2.2) •
        ((1+strictCoefficientMap p r x.1) • diagonalProjection p q +
          (1+x.2.1) • ((strictCoefficientMap p r).comp (lowerProjection p q))))

theorem relativeLDUTerm_hasFDerivAt {p q : ℕ} (x : FullBand p q) (r s t : ℕ) :
    HasFDerivAt (fun y => relativeLDUTerm y r s t) (relativeLDUTermDerivative x r s t) x := by
  have hL := (hasFDerivAt_const (1 : Seq) x).add
    (((strictCoefficientMap p r).comp (lowerProjection p q)).hasFDerivAt)
  have hD := (hasFDerivAt_const (1 : Seq) x).add ((diagonalProjection p q).hasFDerivAt)
  have hU := (hasFDerivAt_const (1 : Seq) x).add
    (((strictCoefficientMap q s).comp (upperProjection p q)).hasFDerivAt)
  convert (zeroExtension t).hasFDerivAt.comp x ((hL.mul hD).mul hU) using 1 <;>
    first | rfl | (simp only [relativeLDUTermDerivative,zero_add,Pi.add_apply,Pi.mul_apply]; rfl)

def relativeLDUCoefficientDerivative {p q : ℕ} (l : Fin p → ℕ → ℝ) (d : ℕ → ℝ)
    (u : Fin q → ℕ → ℝ) (hl : ∀ i j,0<l i j) (hd : ∀ j,0<d j)
    (hu : ∀ i j,0<u i j) (r s N : ℕ) (x : FullBand p q) : FullBand p q →L[ℝ] Seq :=
  ∑ t ∈ range N,relativeLDUWeight l d u hl hd hu r s N t •
    relativeLDUTermDerivative x (r+t) (s+t) t

theorem relativeLDUCoefficient_hasFDerivAt {p q : ℕ} (l : Fin p → ℕ → ℝ) (d : ℕ → ℝ)
    (u : Fin q → ℕ → ℝ) (hl : ∀ i j,0<l i j) (hd : ∀ j,0<d j)
    (hu : ∀ i j,0<u i j) (r s N : ℕ) (x : FullBand p q) :
    HasFDerivAt (relativeLDUCoefficient l d u hl hd hu r s N)
      (relativeLDUCoefficientDerivative l d u hl hd hu r s N x) x := by
  have h := HasFDerivAt.fun_sum (u := range N) (fun t _ =>
    (relativeLDUTerm_hasFDerivAt x (r+t) (s+t) t).const_mul
      (relativeLDUWeight l d u hl hd hu r s N t))
  convert h.sub_const (1 : Seq) using 1 <;> rfl

def relativeLDUProductDerivative {p q : ℕ} (l : Fin p → ℕ → ℝ) (d : ℕ → ℝ)
    (u : Fin q → ℕ → ℝ) (hl : ∀ i j,0<l i j) (hd : ∀ j,0<d j)
    (hu : ∀ i j,0<u i j) (x : FullBand p q) : FullBand p q →L[ℝ] FullBand p q :=
  (ContinuousLinearMap.pi fun r => relativeLDUCoefficientDerivative l d u hl hd hu (r.val+1) 0 (q+1) x).prod
    ((relativeLDUCoefficientDerivative l d u hl hd hu 0 0 (q+1) x).prod
      (ContinuousLinearMap.pi fun s => relativeLDUCoefficientDerivative l d u hl hd hu 0 (s.val+1) (p+1) x))

theorem relativeLDUProduct_hasFDerivAt {p q : ℕ} (l : Fin p → ℕ → ℝ) (d : ℕ → ℝ)
    (u : Fin q → ℕ → ℝ) (hl : ∀ i j,0<l i j) (hd : ∀ j,0<d j)
    (hu : ∀ i j,0<u i j) (x : FullBand p q) :
    HasFDerivAt (relativeLDUProduct l d u hl hd hu) (relativeLDUProductDerivative l d u hl hd hu x) x := by
  have hL := hasFDerivAt_pi.mpr fun r : Fin p => relativeLDUCoefficient_hasFDerivAt l d u hl hd hu (r.val+1) 0 (q+1) x
  have hD := relativeLDUCoefficient_hasFDerivAt l d u hl hd hu 0 0 (q+1) x
  have hU := hasFDerivAt_pi.mpr fun s : Fin q => relativeLDUCoefficient_hasFDerivAt l d u hl hd hu 0 (s.val+1) (p+1) x
  convert hL.prodMk (hD.prodMk hU) using 1 <;> rfl

theorem relativeLDUTermDerivative_zero_apply {p q : ℕ} (h : FullBand p q) (r s t j : ℕ) :
    relativeLDUTermDerivative (0 : FullBand p q) r s t h j =
      if t≤j then strictCoefficientMap p r h.1 (j-t)+h.2.1 (j-t)+strictCoefficientMap q s h.2.2 (j-t) else 0 := by
  change (zeroExtension t (_)) j=_
  simp only [zeroExtension_apply,initialExtension]
  split_ifs
  · simp [lowerProjection,upperProjection,diagonalProjection,smul_eq_mul]
    ring
  · rfl

def rawLDUDerivative {p q : ℕ} (l : Fin p → ℕ → ℝ) (d : ℕ → ℝ)
    (u : Fin q → ℕ → ℝ) (h : FullBand p q) (r s N j : ℕ) : ℝ :=
  ∑ t ∈ range N,rawLDUTerm l d u r s t j *
    (if t≤j then strictCoefficientMap p (r+t) h.1 (j-t)+h.2.1 (j-t)+
      strictCoefficientMap q (s+t) h.2.2 (j-t) else 0)

theorem relativeLDUCoefficientDerivative_actual {p q : ℕ} (l : Fin p → ℕ → ℝ) (d : ℕ → ℝ)
    (u : Fin q → ℕ → ℝ) (hl : ∀ i j,0<l i j) (hd : ∀ j,0<d j)
    (hu : ∀ i j,0<u i j) (r s N : ℕ) (hr : r≤p) (hs : s≤q) (hN : 0<N)
    (h : FullBand p q) (j : ℕ) :
    rawLDUSum l d u r s N j * relativeLDUCoefficientDerivative l d u hl hd hu r s N 0 h j =
      rawLDUDerivative l d u h r s N j := by
  have hne := ne_of_gt (rawLDUSum_pos l d u hl hd hu r s N j hr hs hN)
  simp only [relativeLDUCoefficientDerivative,_root_.sum_apply,
    _root_.smul_apply,BoundedContinuousFunction.sum_apply,
    smul_eq_mul,BoundedContinuousFunction.mul_apply,Finset.mul_sum,rawLDUDerivative]
  apply sum_congr rfl
  intro t ht
  rw [relativeLDUWeight_apply l d u hl hd hu r s N t j (mem_range.mp ht),
    relativeLDUTermDerivative_zero_apply]
  field_simp

theorem relativeLDUProductDerivative_lower_actual {p q : ℕ}
    (l : Fin p → ℕ → ℝ) (d : ℕ → ℝ) (u : Fin q → ℕ → ℝ)
    (hl : ∀ i j,0<l i j) (hd : ∀ j,0<d j) (hu : ∀ i j,0<u i j)
    (h : FullBand p q) (r : Fin p) (j : ℕ) :
    rawLDUSum l d u (r.val+1) 0 (q+1) j *
      (relativeLDUProductDerivative l d u hl hd hu 0 h).1 r j =
      rawLDUDerivative l d u h (r.val+1) 0 (q+1) j :=
  relativeLDUCoefficientDerivative_actual l d u hl hd hu _ _ _ (by omega) (by omega) (by omega) h j

theorem relativeLDUProductDerivative_diagonal_actual {p q : ℕ}
    (l : Fin p → ℕ → ℝ) (d : ℕ → ℝ) (u : Fin q → ℕ → ℝ)
    (hl : ∀ i j,0<l i j) (hd : ∀ j,0<d j) (hu : ∀ i j,0<u i j)
    (h : FullBand p q) (j : ℕ) :
    rawLDUSum l d u 0 0 (q+1) j *
      (relativeLDUProductDerivative l d u hl hd hu 0 h).2.1 j =
      rawLDUDerivative l d u h 0 0 (q+1) j :=
  relativeLDUCoefficientDerivative_actual l d u hl hd hu _ _ _ (by omega) (by omega) (by omega) h j

theorem relativeLDUProductDerivative_upper_actual {p q : ℕ}
    (l : Fin p → ℕ → ℝ) (d : ℕ → ℝ) (u : Fin q → ℕ → ℝ)
    (hl : ∀ i j,0<l i j) (hd : ∀ j,0<d j) (hu : ∀ i j,0<u i j)
    (h : FullBand p q) (s : Fin q) (j : ℕ) :
    rawLDUSum l d u 0 (s.val+1) (p+1) j *
      (relativeLDUProductDerivative l d u hl hd hu 0 h).2.2 s j =
      rawLDUDerivative l d u h 0 (s.val+1) (p+1) j :=
  relativeLDUCoefficientDerivative_actual l d u hl hd hu _ _ _ (by omega) (by omega) (by omega) h j

#print axioms analytic_relativeLDUProduct
#print axioms relativeLDUCoefficient_actual
#print axioms relativeLDUProduct_hasFDerivAt
#print axioms relativeLDUCoefficientDerivative_actual

end BTP.RelativeStability
