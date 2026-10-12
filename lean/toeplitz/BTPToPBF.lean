import MetelmannFromFlags
import LowerOperatorBridge
import ForwardConversion
import ManuscriptTheorem

/-! Direct BTP -> global bounded PBF. There is NO ASW/Edrei hypothesis.
The proof constructs Metelmann factors for the triangular coefficient matrix,
removes their initial zeros by an exact Toeplitz shift, converts q factors
to upper factors, and applies the already proved positive exchanges. -/

open Matrix Finset Polynomial
noncomputable section
namespace BTP.Toeplitz

theorem BTP_shift_to_triangular {p q : ℕ} (P : ℝ[X])
    (h : StrictBandTP p q (symbolMatrix q P)) :
    StrictBandTP (p+q) 0 (symbolMatrix 0 P) := by
  intro k I J hI hJ hadm
  let J' : Fin k → ℕ := fun i => J i+q
  have he : (symbolMatrix q P).submatrix I J' = (symbolMatrix 0 P).submatrix I J := by
    ext i j
    simp [symbolMatrix,J',show I i+q-(J j+q)=I i-J j by omega]
  rw [← he]
  apply h I J' hI (fun i j hij => Nat.add_lt_add_right (hJ hij) q)
  intro i
  have hi := hadm i
  constructor <;> dsimp [J'] <;> omega

theorem symbolMatrix_C_mul (c : ℝ) (P : ℝ[X]) :
    symbolMatrix 0 (C c * P) = fun i j => c * symbolMatrix 0 P i j := by
  ext i j
  simp only [symbolMatrix, Nat.add_zero, coeff_C_mul]
  split_ifs <;> simp

theorem BTP_C_mul {m : ℕ} (P : ℝ[X]) {c : ℝ} (hc : 0 < c)
    (h : StrictBandTP m 0 (symbolMatrix 0 P)) :
    StrictBandTP m 0 (symbolMatrix 0 (C c*P)) := by
  intro k I J hI hJ hadm
  rw [symbolMatrix_C_mul]
  have he := Matrix.det_mul_column (fun _ : Fin k => c) ((symbolMatrix 0 P).submatrix I J)
  change Matrix.det (fun i j : Fin k => c * symbolMatrix 0 P (I i) (J j)) = _ at he
  change 0 < Matrix.det (fun i j : Fin k => c * symbolMatrix 0 P (I i) (J j))
  rw [he]
  exact mul_pos (prod_pos (fun _ _ => hc)) (h I J hI hJ hadm)

/-- The desired implication, directly from the manuscript's BTP definition. -/
theorem BTP_implies_global_bounded_PBF (p q : ℕ) (hpq : 0 < p+q) (P : ℝ[X])
    (hdeg : P.natDegree ≤ p+q) (hzero : 0 < P.coeff 0)
    (hBTP : StrictBandTP p q (symbolMatrix q P)) :
    HasBoundedPBF p q (symbolOperator q P) := by
  let m := p+q
  let ω := P.coeff 0
  let N := C ω⁻¹ * P
  let F := symbolMatrix 0 N
  have hω : 0 < ω := hzero
  have hN0 : N.coeff 0 = 1 := by simp [N,ω,hzero.ne']
  have hNdeg : N.natDegree ≤ m := (natDegree_C_mul_le _ P).trans hdeg
  have hF : ∀ d, Extraction.UnitLower d F := by
    intro d
    constructor
    · intro n _; simp [F,symbolMatrix,hN0]
    · intro n _ j _ hnj; simp [F,symbolMatrix,show ¬ j ≤ n by omega]
  have hb : ∀ d, Extraction.Bandwidth d m F := by
    intro d n _ j _ hjn
    exact symbolMatrix_band m 0 N (by simpa using hNdeg) n j (Or.inl hjn)
  have hTP : StrictBandTP m 0 F :=
    BTP_C_mul P (inv_pos.mpr hω) (BTP_shift_to_triangular P hBTP)
  obtain ⟨a,ha,hprod⟩ := SemiInfinite.metelmann_from_BTP m hpq F hF hb hTP
  have he : Extraction.productEntries a m = F := by
    funext i j
    let d := max i j+1
    have hi : i < d := by dsimp [d]; omega
    have hj : j < d := by dsimp [d]; omega
    have h := congrArg (fun M : Matrix (Fin d) (Fin d) ℝ => M ⟨i,hi⟩ ⟨j,hj⟩) (hprod d)
    simpa only [BTP.lowerProduct_entry,Extraction.productEntries,Extraction.finiteMatrix,
      Matrix.of_apply] using h
  have ht : ∀ n j s, Extraction.productEntries a m (n+s) (j+s) =
      Extraction.productEntries a m n j := by
    intro n j s
    rw [congrFun (congrFun he (n+s)) (j+s),congrFun (congrFun he n) j]
    simp [F,symbolMatrix,show n+s-(j+s)=n-j by omega]
  let b := shiftEntries a m
  have hbnd : ∀ j < m, BoundedPositive (b j) :=
    fun j hj => shifted_metelmann_bounded hpq ha ht hj
  have he' : Extraction.productEntries b m = F := by
    have h := (SemiInfinite.sameProduct_iff_entries m b a).mp (shifted_same_product ht m)
    exact h.trans he
  let as := (List.range m).reverse.map b
  have hlen : as.length = p+q := by simp [as,m]
  have has : ∀ a ∈ as, BoundedPositive a := by
    intro c hc
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hc
    exact hbnd j (List.mem_range.mp (List.mem_reverse.mp hj))
  have hop : lowerProduct as = aeval backward N := by
    rw [← familyOperator_list]
    exact operator_of_triangular_entries b m N he'
  have hP : C ω * N = P := by
    dsimp [N]
    rw [← mul_assoc,← map_mul,mul_inv_cancel₀ hω.ne',map_one,one_mul]
  have hpe : aeval backward P = diagonal (fun _ => ω) * lowerProduct as := by
    rw [hop,← algebraMap_op,← aeval_C,← map_mul,hP]
  have h := triangular_factorization_to_PBF as p q hlen has ω hω
  have hOp : symbolOperator q P = diagonal (fun _ => ω) * forward^q * lowerProduct as := by
    rw [symbolOperator,hpe,← mul_assoc,← constant_diagonal_commutes]
  rwa [hOp]

/-- Literal coefficients t(i-j), with exactly the bandwidths and hypotheses
of the manuscript. ASW, negative roots and a prior factorization are absent. -/
theorem manuscript_BTP_to_PBF {p q : ℕ} (D : ToeplitzData p q)
    (hpq : 0 < p+q) (hBTP : StrictBandTP p q D.matrix) : MatrixBoundedPBF p q D.matrix := by
  have ht : StrictBandTP p q (symbolMatrix q D.polynomial) := by
    rwa [D.symbol_matrix]
  refine ⟨symbolOperator q D.polynomial,
    BTP_implies_global_bounded_PBF p q hpq D.polynomial D.polynomial_degree.le D.polynomial_zero_pos ht,?_⟩
  rw [symbolOperator_matrix,D.symbol_matrix]

theorem manuscript_BTP_iff_PBF {p q : ℕ} (D : ToeplitzData p q) (hpq : 0 < p+q) :
    StrictBandTP p q D.matrix ↔ MatrixPBF p q D.matrix := by
  constructor
  · intro ht
    exact matrixBoundedPBF_implies_PBF (manuscript_BTP_to_PBF D hpq ht)
  · rintro ⟨A,ha,he⟩
    rw [← he]
    exact (PBF_implies_BTP ha).2

#print manuscript_BTP_to_PBF
#print axioms manuscript_BTP_to_PBF
#print axioms manuscript_BTP_iff_PBF
end BTP.Toeplitz
