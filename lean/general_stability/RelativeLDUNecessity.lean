import RelativeFullTransfer
import RelativeNormalizedControl
import RelativeRowSums

/-! Necessity of the cross condition in relative LDU, without any bounds
on the original matrix or factor entries. -/
noncomputable section
set_option maxHeartbeats 1000000
open Finset
open scoped BigOperators
namespace BTP.RelativeStability
open BTP BTP.InverseBounds BTP.GeneralStability BTP.Stability BTP.Stability.BandLDU BTP.SemiInfinite

/-- The bounded relative perturbation whose actual matrix is D. -/
def relativeDiagonalDirection {p q : ℕ}
    (l : Fin p → ℕ → ℝ) (d : ℕ → ℝ) (u : Fin q → ℕ → ℝ)
    (hl : ∀ i n,0 < l i n) (hd : ∀ n,0 < d n) (hu : ∀ i n,0 < u i n) : FullBand p q :=
  (0,relativeLDUWeight l d u hl hd hu 0 0 (q+1) 0,0)

theorem relativeDiagonalDirection_actual {p q N : ℕ}
    (l : Fin p → ℕ → ℝ) (d : ℕ → ℝ) (u : Fin q → ℕ → ℝ)
    (hl : ∀ i n,0 < l i n) (hd : ∀ n,0 < d n) (hu : ∀ i n,0 < u i n) :
    (fun i j : Fin N => rawFullEntry l d u i.val j.val*
      fullEntry (relativeDiagonalDirection l d u hl hd hu) i.val j.val)=
      Matrix.diagonal (fun i : Fin N=>d i.val) := by
  ext i j
  by_cases he : i=j
  · subst j
    simp only [fullEntry_diag,relativeDiagonalDirection,Matrix.diagonal_apply_eq]
    rw [relativeLDUWeight_apply _ _ _ _ _ _ _ _ _ _ _ (by omega)]
    have ht : rawLDUTerm l d u 0 0 0 i.val=d i.val := by simp [rawLDUTerm,rawTriangular]
    rw [ht]
    have hf : rawFullEntry l d u i.val i.val=rawLDUSum l d u 0 0 (q+1) i.val := by
      simpa using rawFullEntry_lower l d u 0 i.val
    rw [hf,mul_div_cancel₀ _ (ne_of_gt (rawLDUSum_pos l d u hl hd hu 0 0 (q+1) i.val
      (by omega) (by omega) (by omega)))]
  · have hv : i.val≠j.val := fun h=>he (Fin.ext h)
    simp [fullEntry,relativeDiagonalDirection,bandEntry,hv,he]

/-- A weighted version of the signed-inverse diagonal identity. -/
theorem signed_inverse_weighted_diagonal {N : ℕ}
    (Li Ui Q R : Mat N) (σ d : Fin N → ℝ)
    (hσ : ∀ i,σ i*σ i=1)
    (hQ : ∀ i j,Li i j=σ i*Q i j*σ j)
    (hR : ∀ i j,Ui i j=σ i*R j i*σ j) (i : Fin N) :
    (Li*Matrix.diagonal d*Ui) i i=∑ s,Q i s*R i s*d s := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal]
  apply sum_congr rfl
  intro s _
  rw [hQ,hR]
  calc
    _=(σ i*σ i)*(σ s*σ s)*(Q i s*R i s*d s) := by ring
    _=_ := by rw [hσ,hσ];ring

/-- A bounded relative solution in the D direction bounds all weighted
joint inverse row sums. This is the necessity estimate used below. -/
theorem relative_rows_bound_of_diagonal_solution {p q : ℕ}
    (a : Fin p → ℕ → ℝ) (d : ℕ → ℝ) (b : Fin q → ℕ → ℝ)
    (ha : ∀ i n,0 < a i n) (hd : ∀ n,0 < d n) (hb : ∀ i n,0 < b i n)
    (h : FullBand p q)
    (he : relativeLDUProductDerivative (relativeFactorBase a) d (relativeFactorBase b)
      (relativeFactorBase_pos a ha) hd (relativeFactorBase_pos b hb) 0 h=
      relativeDiagonalDirection (relativeFactorBase a) d (relativeFactorBase b)
        (relativeFactorBase_pos a ha) hd (relativeFactorBase_pos b hb)) :
    ∀ n,relativeJointRow (rawReverse (extendRaw a) p) (rawReverse (extendRaw b) q) p q d n≤‖h‖ := by
  intro n
  let aa:=rawReverse (extendRaw a) p
  let bb:=rawReverse (extendRaw b) q
  let N:=n+1
  let ii : Fin N:=⟨n,by dsimp [N];omega⟩
  let S:=actualData aa bb p q d (fun n=>ne_of_gt (hd n))
  have hL : (fun i j : Fin N=>rawUnitEntry (relativeFactorBase a) i.val j.val)=S.L N :=
    rawUnitEntry_productBand_finite (extendRaw a) p N
  have hU : (fun i j : Fin N=>rawUnitEntry (relativeFactorBase b) j.val i.val)=S.U N := by
    have hh:=rawUnitEntry_productBand_finite (extendRaw b) q N
    exact congrArg Matrix.transpose hh
  let X : Mat N:=fun i j=>S.L N i j*bandEntry h.1 i.val j.val
  let Z : Mat N:=Matrix.diagonal (fun i : Fin N=>d i.val*h.2.1 i.val)
  let Y : Mat N:=fun i j=>S.U N i j*bandEntry h.2.2 j.val i.val
  have hX : StrictLower X := by
    intro i j hij
    dsimp [X]
    rw [bandEntry_upper _ hij]
    ring
  have hY : StrictUpper Y := by
    intro i j hij
    dsimp [Y]
    rw [bandEntry_upper _ hij]
    ring
  have hZ : Diag Z := by
    intro i j hij
    simp [Z,Matrix.diagonal,hij]
  have hv : variation (S.L N) (Matrix.diagonal (fun i : Fin N=>d i.val)) (S.U N) X Z Y=
      Matrix.diagonal (fun i : Fin N=>d i.val) := by
    have hh:=relativeLDUProductDerivative_section (relativeFactorBase a) d (relativeFactorBase b)
      (relativeFactorBase_pos a ha) hd (relativeFactorBase_pos b hb) h N
    rw [he,relativeDiagonalDirection_actual] at hh
    have hx : X=(fun i j : Fin N=>rawUnitEntry (relativeFactorBase a) i.val j.val*bandEntry h.1 i.val j.val) := by
      ext i j
      exact congrArg (fun M : Mat N=>M i j*bandEntry h.1 i.val j.val) hL.symm
    have hy : Y=(fun i j : Fin N=>rawUnitEntry (relativeFactorBase b) j.val i.val*bandEntry h.2.2 j.val i.val) := by
      ext i j
      exact congrArg (fun M : Mat N=>M i j*bandEntry h.2.2 j.val i.val) hU.symm
    rw [hx,hy]
    rw [hL,hU] at hh
    exact hh.symm
  have hz:=variation_diagonal (S.L N) (S.Li N) (S.U N) (S.Ui N) X Z Y
    (fun i : Fin N=>d i.val) (S.Li_L N) (S.U_Ui N) (S.lower_Li N) (S.upper_Ui N) hX hZ hY
  rw [hv] at hz
  have hn:=congrArg (fun M : Mat N=>M ii ii) hz
  simp only [Z,diagPart,Matrix.diagonal_apply_eq] at hn
  have hs:=signed_inverse_weighted_diagonal (S.Li N) (S.Ui N)
    (fun i j : Fin N=>inverseEntries aa p i.val j.val)
    (fun i j : Fin N=>inverseEntries bb q i.val j.val)
    (fun i : Fin N=>(-1:ℝ)^i.val) (fun i : Fin N=>d i.val)
    (fun i=>sign_square i.val)
    (fun i j=>(actualInverse_finite aa p N i j).symm)
    (by intro i j;dsimp [S,actualData];rw [←actualInverse_finite];dsimp [actualInverse];ring) ii
  rw [hs] at hn
  change d n*h.2.1 n=∑ s : Fin (n+1),inverseEntries aa p n s.val*inverseEntries bb q n s.val*d s.val at hn
  rw [Fin.sum_univ_eq_sum_range (fun s=>inverseEntries aa p n s*inverseEntries bb q n s*d s) (n+1)] at hn
  have hr : relativeJointRow aa bb p q d n=h.2.1 n := by
    unfold relativeJointRow
    rw [←sum_div,←hn]
    exact mul_div_cancel_left₀ _ (ne_of_gt (hd n))
  change relativeJointRow aa bb p q d n≤‖h‖
  rw [hr]
  exact (le_abs_self _).trans ((boundedSequence_abs_le h.2.1 n).trans
    ((le_max_left _ _).trans (le_max_right _ _)))

/-- Relative analytic LDU forces geometric decay of the genuine crossed
factor weight, including the ratio of consecutive pivots. -/
theorem relative_analytic_ldu_implies_cross {p q : ℕ}
    (a : Fin (p+1) → ℕ → ℝ) (d : ℕ → ℝ) (b : Fin (q+1) → ℕ → ℝ)
    (ha : ∀ i n,0 < a i n) (hd : ∀ n,0 < d n) (hb : ∀ i n,0 < b i n)
    (hc : RelativeAnalyticLDUSection (relativeFactorBase a) d (relativeFactorBase b)
      (relativeFactorBase_pos a ha) hd (relativeFactorBase_pos b hb)) :
    GeometricDecay (crossWeight (a ⟨p,by omega⟩) (b ⟨q,by omega⟩) d) := by
  obtain ⟨R,hR⟩:=relative_analytic_ldu_derivative_rightInverse (relativeFactorBase a) d
    (relativeFactorBase b) (relativeFactorBase_pos a ha) hd (relativeFactorBase_pos b hb) hc
  let E:=relativeDiagonalDirection (relativeFactorBase a) d (relativeFactorBase b)
    (relativeFactorBase_pos a ha) hd (relativeFactorBase_pos b hb)
  have he : relativeLDUProductDerivative (relativeFactorBase a) d (relativeFactorBase b)
      (relativeFactorBase_pos a ha) hd (relativeFactorBase_pos b hb) 0 (R E)=E :=
    congrArg (fun M : FullBand (p+1) (q+1) →L[ℝ] FullBand (p+1) (q+1)=>M E) hR
  have hg:=relative_joint_rows_imply_cross (rawReverse (extendRaw a) (p+1))
    (rawReverse (extendRaw b) (q+1)) p q d
    (fun i _ n=>extendRaw_pos a ha _ n) (fun i _ n=>extendRaw_pos b hb _ n) hd
    ⟨‖R E‖,relative_rows_bound_of_diagonal_solution a d b ha hd hb (R E) he⟩
  have hpa : rawReverse (extendRaw a) (p+1) 0=a ⟨p,by omega⟩ := by
    funext n
    simp only [rawReverse,Nat.add_sub_cancel,Nat.sub_zero,extendRaw,show p<p+1 by omega,↓reduceDIte]
  have hpb : rawReverse (extendRaw b) (q+1) 0=b ⟨q,by omega⟩ := by
    funext n
    simp only [rawReverse,Nat.add_sub_cancel,Nat.sub_zero,extendRaw,show q<q+1 by omega,↓reduceDIte]
  rw [hpa,hpb] at hg
  exact hg

/-- The crossed geometric condition is necessary for relative analytic
positive bidiagonal factor choices in the full band. -/
theorem relative_full_positive_choice_implies_cross {p q : ℕ}
    (a : Fin (p+1) → ℕ → ℝ) (d : ℕ → ℝ) (b : Fin (q+1) → ℕ → ℝ)
    (ha : ∀ i n,0 < a i n) (hd : ∀ n,0 < d n) (hb : ∀ i n,0 < b i n)
    (hc : RelativeFullPositiveAnalyticChoice a d b ha hd hb) :
    GeometricDecay (crossWeight (a ⟨p,by omega⟩) (b ⟨q,by omega⟩) d) :=
  relative_analytic_ldu_implies_cross a d b ha hd hb
    (relative_full_choice_implies_analytic_ldu a d b ha hd hb hc)

#print axioms relative_full_positive_choice_implies_cross

#print axioms relative_rows_bound_of_diagonal_solution
#print axioms relative_analytic_ldu_implies_cross
end BTP.RelativeStability
