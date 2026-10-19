import RelativeActualControl
import RelativeLDUInverse
import RelativeLDUScaling

noncomputable section
namespace BTP.RelativeStability
open Finset Matrix BTP BTP.Stability BTP.Stability.BandLDU BTP.GeneralStability
variable {N : ℕ}
local instance : PartialOrder (Mat N) := inferInstanceAs (PartialOrder (Fin N → Fin N → ℝ))

def normalizedRelativeData (a b : ℕ → ℕ → ℝ) (p q : ℕ) (d : ℕ → ℝ)
    (ha : ∀ i n,0 < a i n) (hb : ∀ i n,0 < b i n) (hd : ∀ n,0 < d n) :
    RelativeLDUData (rawProductBand (normalizedLast a (p+1)) (p+1))
      (scaleDiagonal d (cumulativeWeight (a p)) (cumulativeWeight (b q)))
      (rawProductBand (normalizedLast b (q+1)) (q+1)) where
  s := normalizedData a b p q d ha hb hd
  lower_eq := fun N => (rawUnitEntry_productBand_finite (normalizedLast a (p+1)) (p+1) N).symm
  upper_eq := by
    intro N
    ext i j
    exact (congrArg (fun M : Mat N => M j i)
      (rawUnitEntry_productBand_finite (normalizedLast b (q+1)) (q+1) N)).symm
  diagonal_eq := rfl

theorem RelativeLDUData.rawFullEntry_eq {p q : ℕ} {l : Fin p → ℕ → ℝ}
    {d : ℕ → ℝ} {u : Fin q → ℕ → ℝ} (S : RelativeLDUData l d u)
    (N : ℕ) (i j : Fin N) :
    rawFullEntry l d u i.val j.val=(S.s.L N*Matrix.diagonal (fun k : Fin N => d k.val)*S.s.U N) i j := by
  rw [rawFullEntry_fin,S.lower_eq,S.upper_eq]
  change (∑ k : Fin N,rawUnitEntry l i.val k.val*d k.val*rawUnitEntry u j.val k.val) =
    ∑ k : Fin N,(∑ z : Fin N,rawUnitEntry l i.val z.val*
      (Matrix.diagonal (fun t : Fin N => d t.val)) z k)*rawUnitEntry u j.val k.val
  simp [Matrix.diagonal]

theorem normalized_inverse_relative_bounds (a b : ℕ → ℕ → ℝ) (p q : ℕ) (d : ℕ → ℝ)
    (ha : ∀ i n,0 < a i n) (hb : ∀ i n,0 < b i n) (hd : ∀ n,0 < d n)
    (hga : ∀ i,i+1 < p+1 → GeometricDecay (fun n => a i n/a (i+1) n))
    (hgb : ∀ i,i+1 < q+1 → GeometricDecay (fun n => b i n/b (i+1) n))
    (hcross : GeometricDecay (crossWeight (a p) (b q) d)) :
    ∃ C : ℝ,0 ≤ C ∧ (normalizedRelativeData a b p q d ha hb hd).Bounds C := by
  obtain ⟨A,B,K,Z,hA,hB,hK,hZ,hcontrol⟩ := normalized_finite_control a b p q d ha hb hd hga hgb hcross
  let S := normalizedRelativeData a b p q d ha hb hd
  let C := relativeFiniteConstant (p+1) (q+1) A B K Z
  refine ⟨C,relativeFiniteConstant_nonneg _ _ _ _ _ _ hA hB hK hZ,?_⟩
  have hbounds (E : FullBand (p+1) (q+1)) (N : ℕ) :=
    finite_relative_inverse_bound (S.s.L N) (S.s.U N) (S.s.Li N) (S.s.Ui N)
      (fun i : Fin N => S.s.d i.val) hA hB hK hZ (hcontrol N) (S.forcing E N) (norm_nonneg E)
  have hforcing (E : FullBand (p+1) (q+1)) (N : ℕ) (i j : Fin N) :
      |S.forcing E N i j| ≤ ‖E‖*(S.s.L N*Matrix.diagonal (fun k : Fin N => S.s.d k.val)*S.s.U N) i j := by
    have hc := hcontrol N
    have hT : 0 ≤ S.s.L N*Matrix.diagonal (fun k : Fin N => S.s.d k.val)*S.s.U N :=
      matrix_mul_nonneg _ _ (matrix_mul_nonneg _ _ hc.nonnegL (by
        intro i j
        by_cases h : i=j
        · subst j
          simp only [Matrix.zero_apply,Matrix.diagonal_apply_eq]
          exact (hc.positiveD i).le
        · simp [Matrix.diagonal,h])) hc.nonnegU
    have he := S.rawFullEntry_eq N i j
    change |rawFullEntry _ _ _ i.val j.val*fullEntry E i.val j.val| ≤ _
    change rawFullEntry _ _ _ i.val j.val=(S.s.L N*Matrix.diagonal (fun k : Fin N => S.s.d k.val)*S.s.U N) i j at he
    rw [he,abs_mul,abs_of_nonneg (hT i j)]
    exact (mul_le_mul_of_nonneg_left (fullEntry_abs_le E i.val j.val) (hT i j)).trans_eq (mul_comm _ _)
  constructor
  · intro E N i j
    by_cases hji : j ≤ i
    · have hh := (hbounds E N (hforcing E N)).1 i j hji
      change |S.invX E N i j| ≤ C*‖E‖*_
      change |S.invX E N i j| ≤ ‖E‖*C*S.s.L N i j at hh
      rw [S.lower_eq] at hh
      simpa only [mul_comm ‖E‖ C] using hh
    · have hz := (S.inv_triangular E N).1 i j (le_of_lt (lt_of_not_ge hji))
      rw [hz]
      simp [rawUnitEntry,show ¬j.val ≤ i.val from hji]
  · intro E N i
    have hh := (hbounds E N (hforcing E N)).2.1 i
    change |S.invV E N i i| ≤ ‖E‖*C*S.s.d i.val at hh
    simp only [RelativeLDUData.invZ,diagPart,Matrix.diagonal_apply_eq]
    rw [mul_comm ‖E‖ C] at hh
    exact hh
  · intro E N i j
    by_cases hij : i ≤ j
    · have hh := (hbounds E N (hforcing E N)).2.2 i j hij
      change |S.invY E N i j| ≤ C*‖E‖*_
      change |S.invY E N i j| ≤ ‖E‖*C*S.s.U N i j at hh
      rw [S.upper_eq] at hh
      simpa only [mul_comm ‖E‖ C] using hh
    · have hz := (S.inv_triangular E N).2.2 i j (le_of_lt (lt_of_not_ge hij))
      rw [hz]
      simp [rawUnitEntry,show ¬i.val ≤ j.val from hij]

theorem rawProductBand_normalized (c : ℕ → ℕ → ℝ) (hc : ∀ i n,0 < c i n) (p : ℕ) :
    rawProductBand (normalizedLast c (p+1)) (p+1)=
      scaleTriangular (rawProductBand c (p+1)) (cumulativeWeight (c p)) := by
  funext r j
  change rawCoefficient (normalizeRaw c (c p)) (p+1) (r.val+1) j = _
  rw [normalizeRaw_rawCoefficient c (c p) (hc p),blockProduct_ratio (c p) (hc p)]
  simp only [scaleTriangular,rawProductBand,cumulativeWeight,show j+(r.val+1)=j+r.val+1 by omega]
  field_simp

theorem relativeLDUProduct_congr_bases {p q : ℕ}
    (l l' : Fin p → ℕ → ℝ) (d : ℕ → ℝ) (u u' : Fin q → ℕ → ℝ)
    (hl : ∀ i n,0<l i n) (hl' : ∀ i n,0<l' i n)
    (hd : ∀ n,0<d n) (hu : ∀ i n,0<u i n) (hu' : ∀ i n,0<u' i n)
    (heL : l=l') (heU : u=u') :
    relativeLDUProduct l d u hl hd hu=relativeLDUProduct l' d u' hl' hd hu' := by
  subst l'
  subst u'
  rfl

theorem relative_ldu_analytic_of_geometric_raw (a b : ℕ → ℕ → ℝ) (p q : ℕ) (d : ℕ → ℝ)
    (ha : ∀ i n,0 < a i n) (hb : ∀ i n,0 < b i n) (hd : ∀ n,0 < d n)
    (hga : ∀ i,i+1 < p+1 → GeometricDecay (fun n => a i n/a (i+1) n))
    (hgb : ∀ i,i+1 < q+1 → GeometricDecay (fun n => b i n/b (i+1) n))
    (hcross : GeometricDecay (crossWeight (a p) (b q) d)) :
    RelativeAnalyticLDUSection (rawProductBand a (p+1)) d (rawProductBand b (q+1))
      (rawProductBand_pos a ha _) hd (rawProductBand_pos b hb _) := by
  obtain ⟨C,_,hbound⟩ := normalized_inverse_relative_bounds a b p q d ha hb hd hga hgb hcross
  have hs := (normalizedRelativeData a b p q d ha hb hd).analyticSection_of_bounds
    (rawProductBand_pos _ (normalizedLast_pos a ha (p+1)) _)
    (scaleDiagonal_pos d _ _ hd (cumulativeWeight_pos (a p) (ha p)) (cumulativeWeight_pos (b q) (hb q)))
    (rawProductBand_pos _ (normalizedLast_pos b hb (q+1)) _) C hbound
  have he := relativeLDUProduct_scale (rawProductBand a (p+1)) d (rawProductBand b (q+1))
    (rawProductBand_pos a ha _) hd (rawProductBand_pos b hb _)
    (cumulativeWeight (a p)) (cumulativeWeight (b q))
    (cumulativeWeight_pos (a p) (ha p)) (cumulativeWeight_pos (b q) (hb q))
  have he0 := relativeLDUProduct_congr_bases
    (rawProductBand (normalizedLast a (p+1)) (p+1))
    (scaleTriangular (rawProductBand a (p+1)) (cumulativeWeight (a p)))
    (scaleDiagonal d (cumulativeWeight (a p)) (cumulativeWeight (b q)))
    (rawProductBand (normalizedLast b (q+1)) (q+1))
    (scaleTriangular (rawProductBand b (q+1)) (cumulativeWeight (b q)))
    (rawProductBand_pos _ (normalizedLast_pos a ha _) _)
    (scaleTriangular_pos _ _ (rawProductBand_pos a ha _) (cumulativeWeight_pos _ (ha p)))
    (scaleDiagonal_pos _ _ _ hd (cumulativeWeight_pos _ (ha p)) (cumulativeWeight_pos _ (hb q)))
    (rawProductBand_pos _ (normalizedLast_pos b hb _) _)
    (scaleTriangular_pos _ _ (rawProductBand_pos b hb _) (cumulativeWeight_pos _ (hb q)))
    (rawProductBand_normalized a ha p) (rawProductBand_normalized b hb q)
  have heall := he0.trans he
  rcases hs with ⟨f,hf,hf0,hfr⟩
  refine ⟨f,hf,hf0,?_⟩
  simpa only [heall] using hfr

#print axioms relative_ldu_analytic_of_geometric_raw
end BTP.RelativeStability
