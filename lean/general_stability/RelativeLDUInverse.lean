import RelativeFullTransfer
import BoundedLDUInverse

noncomputable section
open Matrix Finset
open scoped BigOperators
namespace BTP.RelativeStability
open BTP.GeneralStability BTP.Stability.BandLDU

/-- Only algebraic, finite triangular inverses are stored here. No bounded
inverse or analytic section is part of these data. -/
structure RelativeLDUData {p q : ℕ} (l : Fin p → ℕ → ℝ) (d : ℕ → ℝ) (u : Fin q → ℕ → ℝ) where
  s : SectionData
  lower_eq : ∀ N,s.L N=fun i j=>rawUnitEntry l i.val j.val
  upper_eq : ∀ N,s.U N=fun i j=>rawUnitEntry u j.val i.val
  diagonal_eq : s.d=d

namespace RelativeLDUData
variable {p q : ℕ} {l : Fin p → ℕ → ℝ} {d : ℕ → ℝ} {u : Fin q → ℕ → ℝ}

def forcing (_S : RelativeLDUData l d u) (E : FullBand p q) (N : ℕ) : Mat N :=
  fun i j=>rawFullEntry l d u i.val j.val*fullEntry E i.val j.val

def invV (S : RelativeLDUData l d u) (E : FullBand p q) (N : ℕ) : Mat N :=
  S.s.Li N*S.forcing E N*S.s.Ui N
def invX (S : RelativeLDUData l d u) (E : FullBand p q) (N : ℕ) : Mat N :=
  S.s.L N*lowerPart (S.invV E N)*Matrix.diagonal (fun i=>(d i.val)⁻¹)
def invZ (S : RelativeLDUData l d u) (E : FullBand p q) (N : ℕ) : Mat N := diagPart (S.invV E N)
def invY (S : RelativeLDUData l d u) (E : FullBand p q) (N : ℕ) : Mat N :=
  Matrix.diagonal (fun i=>(d i.val)⁻¹)*upperPart (S.invV E N)*S.s.U N

theorem inv_triangular (S : RelativeLDUData l d u) (E : FullBand p q) (N : ℕ) :
    StrictLower (S.invX E N) ∧ Diag (S.invZ E N) ∧ StrictUpper (S.invY E N) :=
  variation_formula_triangular _ _ _ _ (S.s.lower_L N) (S.s.upper_U N)

theorem inv_eq (S : RelativeLDUData l d u) (E : FullBand p q) (N : ℕ) :
    variation (S.s.L N) (Matrix.diagonal (fun i=>d i.val)) (S.s.U N)
      (S.invX E N) (S.invZ E N) (S.invY E N)=S.forcing E N :=
  variation_formula _ _ _ _ _ (S.s.L_Li N) (S.s.Ui_U N)
    (fun i=>by rw [←S.diagonal_eq]; exact S.s.d_ne i.val) _

theorem inv_coherent (S : RelativeLDUData l d u) (E : FullBand p q) (N : ℕ) :
    principal (S.invX E (N+1))=S.invX E N ∧
    principal (S.invZ E (N+1))=S.invZ E N ∧
    principal (S.invY E (N+1))=S.invY E N := by
  have ht := S.inv_triangular E (N+1)
  have he := congrArg principal (S.inv_eq E (N+1))
  rw [principal_variation _ _ _ _ _ _ (S.s.lower_L _) (S.s.upper_U _) ht.1 ht.2.1 ht.2.2,
    S.s.L_coherent,S.s.U_coherent] at he
  change variation (S.s.L N) (Matrix.diagonal (fun i=>d i.val)) (S.s.U N)
    (principal (S.invX E (N+1))) (principal (S.invZ E (N+1)))
    (principal (S.invY E (N+1)))=S.forcing E N at he
  have hu := variation_unique (S.s.L N) (S.s.Li N) (S.s.U N) (S.s.Ui N)
    (principal (S.invX E (N+1))) (principal (S.invZ E (N+1)))
    (principal (S.invY E (N+1))) (fun i=>d i.val)
    (S.s.Li_L N) (S.s.L_Li N) (S.s.U_Ui N) (S.s.Ui_U N)
    (fun i=>by rw [←S.diagonal_eq]; exact S.s.d_ne i.val)
    (S.s.lower_Li N) (S.s.upper_Ui N) (principal_strictLower ht.1)
    (principal_diag ht.2.1) (principal_strictUpper ht.2.2)
  dsimp only at hu
  rw [he] at hu
  exact hu

theorem forcing_add (S : RelativeLDUData l d u) (E F : FullBand p q) (N : ℕ) :
    S.forcing (E+F) N=S.forcing E N+S.forcing F N := by
  ext i j
  simp only [forcing,Matrix.add_apply,fullEntry_add,mul_add]
theorem forcing_smul (S : RelativeLDUData l d u) (c : ℝ) (E : FullBand p q) (N : ℕ) :
    S.forcing (c•E) N=c•S.forcing E N := by
  ext i j
  simp only [forcing,Matrix.smul_apply,fullEntry_smul,smul_eq_mul]
  ring

theorem inv_add (S : RelativeLDUData l d u) (E F : FullBand p q) (N : ℕ) :
    S.invX (E+F) N=S.invX E N+S.invX F N ∧
    S.invZ (E+F) N=S.invZ E N+S.invZ F N ∧
    S.invY (E+F) N=S.invY E N+S.invY F N := by
  simp only [invX,invY,invZ,invV,forcing_add,Matrix.mul_add,Matrix.add_mul,
    lowerPart_add,upperPart_add,diagPart_add,and_self]
theorem inv_smul (S : RelativeLDUData l d u) (c : ℝ) (E : FullBand p q) (N : ℕ) :
    S.invX (c•E) N=c•S.invX E N ∧ S.invZ (c•E) N=c•S.invZ E N ∧
    S.invY (c•E) N=c•S.invY E N := by
  simp only [invX,invY,invZ,invV,forcing_smul,Matrix.mul_smul,Matrix.smul_mul,
    lowerPart_smul,upperPart_smul,diagPart_smul,and_self]

theorem inv_bands (S : RelativeLDUData l d u) (E : FullBand p q) (N : ℕ) :
    LowerBandwidth p (S.invX E N) ∧ UpperBandwidth q (S.invY E N) := by
  apply variation_formula_bands _ _ _ _ _ _ p q (S.s.L_Li N) (S.s.Ui_U N)
  · intro i j hij
    rw [S.lower_eq]
    simp [rawUnitEntry,rawTriangular_outside l (i.val-j.val) j.val (by omega)]
  · intro i j hij
    rw [S.upper_eq]
    simp [rawUnitEntry,rawTriangular_outside u (j.val-i.val) i.val (by omega)]
  · exact S.s.lower_Li N
  · exact S.s.upper_Ui N
  · intro i j hij
    simp [forcing,fullEntry_band E i.val j.val (Or.inl hij)]
  · intro i j hij
    simp [forcing,fullEntry_band E i.val j.val (Or.inr hij)]

def globalX (S : RelativeLDUData l d u) (E : FullBand p q) := coherentEntry (S.invX E)
def globalZ (S : RelativeLDUData l d u) (E : FullBand p q) := coherentEntry (S.invZ E)
def globalY (S : RelativeLDUData l d u) (E : FullBand p q) := coherentEntry (S.invY E)

theorem global_section (S : RelativeLDUData l d u) (E : FullBand p q) (N : ℕ) (i j : Fin N) :
    S.globalX E i.val j.val=S.invX E N i j ∧ S.globalZ E i.val j.val=S.invZ E N i j ∧
    S.globalY E i.val j.val=S.invY E N i j :=
  ⟨coherentEntry_section _ (fun N=>(S.inv_coherent E N).1) N i j,
   coherentEntry_section _ (fun N=>(S.inv_coherent E N).2.1) N i j,
   coherentEntry_section _ (fun N=>(S.inv_coherent E N).2.2) N i j⟩

 end RelativeLDUData

def relativeSequenceMap {p q : ℕ} (f : FullBand p q → ℕ → ℝ) (C : ℝ)
    (hadd : ∀ E F n,f (E+F) n=f E n+f F n)
    (hsmul : ∀ (c : ℝ) E n,f (c•E) n=c*f E n)
    (hbound : ∀ E n,|f E n|≤C*‖E‖) : FullBand p q →L[ℝ] Seq :=
  ({ toFun := fun E=>BTP.Stability.ofAbsBound (f E) (C*‖E‖) (hbound E)
     map_add' := by intro E F; apply BoundedContinuousFunction.ext; exact hadd E F
     map_smul' := by intro c E; apply BoundedContinuousFunction.ext; exact hsmul c E } :
    FullBand p q →ₗ[ℝ] Seq).mkContinuous C
      (fun E=>BoundedContinuousFunction.norm_le_of_nonempty.mpr (hbound E))

namespace RelativeLDUData
variable {p q : ℕ} {l : Fin p → ℕ → ℝ} {d : ℕ → ℝ} {u : Fin q → ℕ → ℝ}

structure Bounds (S : RelativeLDUData l d u) (C : ℝ) : Prop where
  lower : ∀ E N i j,|S.invX E N i j|≤C*‖E‖*rawUnitEntry l i.val j.val
  diagonal : ∀ E N i,|S.invZ E N i i|≤C*‖E‖*d i.val
  upper : ∀ E N i j,|S.invY E N i j|≤C*‖E‖*rawUnitEntry u j.val i.val

theorem rawUnitEntry_coordinate {m : ℕ} (v : Fin m → ℕ → ℝ) (r : Fin m) (j : ℕ) :
    rawUnitEntry v (j+r.val+1) j=v r j := by
  simp only [rawUnitEntry,show j≤j+r.val+1 by omega,↓reduceIte,
    show j+r.val+1-j=r.val+1 by omega,rawTriangular,
    show r.val+1≠0 by omega,show r.val+1≤m by omega,↓reduceDIte,↓reduceIte]
  rfl

theorem global_bounds (S : RelativeLDUData l d u) {C : ℝ} (h : S.Bounds C)
    (E : FullBand p q) (i j : ℕ) :
    |S.globalX E i j|≤C*‖E‖*rawUnitEntry l i j ∧
    |S.globalZ E i i|≤C*‖E‖*d i ∧
    |S.globalY E i j|≤C*‖E‖*rawUnitEntry u j i := by
  exact ⟨h.lower E _ _ _,h.diagonal E _ _,h.upper E _ _ _⟩

theorem global_add (S : RelativeLDUData l d u) (E F : FullBand p q) (i j : ℕ) :
    S.globalX (E+F) i j=S.globalX E i j+S.globalX F i j ∧
    S.globalZ (E+F) i j=S.globalZ E i j+S.globalZ F i j ∧
    S.globalY (E+F) i j=S.globalY E i j+S.globalY F i j := by
  simp only [globalX,globalZ,globalY,coherentEntry,(S.inv_add E F _).1,
    (S.inv_add E F _).2.1,(S.inv_add E F _).2.2,Matrix.add_apply,and_self]

theorem global_smul (S : RelativeLDUData l d u) (c : ℝ) (E : FullBand p q) (i j : ℕ) :
    S.globalX (c•E) i j=c*S.globalX E i j ∧
    S.globalZ (c•E) i j=c*S.globalZ E i j ∧
    S.globalY (c•E) i j=c*S.globalY E i j := by
  simp only [globalX,globalZ,globalY,coherentEntry,(S.inv_smul c E _).1,
    (S.inv_smul c E _).2.1,(S.inv_smul c E _).2.2,Matrix.smul_apply,smul_eq_mul,and_self]

def inverseMap (S : RelativeLDUData l d u)
    (hl : ∀ i j,0<l i j) (hd : ∀ j,0<d j) (hu : ∀ i j,0<u i j)
    (C : ℝ) (hB : S.Bounds C) : FullBand p q →L[ℝ] FullBand p q :=
  (ContinuousLinearMap.pi fun r : Fin p=>
    relativeSequenceMap (fun E j=>S.globalX E (j+r.val+1) j/l r j) C
      (by intro E F j; rw [(S.global_add E F _ _).1,add_div])
      (by intro c E j; rw [(S.global_smul c E _ _).1]; ring)
      (by intro E j
          rw [abs_div,abs_of_pos (hl r j)]
          apply (div_le_iff₀ (hl r j)).mpr
          simpa only [rawUnitEntry_coordinate] using (S.global_bounds hB E (j+r.val+1) j).1)).prod
    ((relativeSequenceMap (fun E j=>S.globalZ E j j/d j) C
      (by intro E F j; rw [(S.global_add E F _ _).2.1,add_div])
      (by intro c E j; rw [(S.global_smul c E _ _).2.1]; ring)
      (by intro E j
          rw [abs_div,abs_of_pos (hd j)]
          exact (div_le_iff₀ (hd j)).mpr (S.global_bounds hB E j j).2.1)).prod
    (ContinuousLinearMap.pi fun r : Fin q=>
      relativeSequenceMap (fun E j=>S.globalY E j (j+r.val+1)/u r j) C
        (by intro E F j; rw [(S.global_add E F _ _).2.2,add_div])
        (by intro c E j; rw [(S.global_smul c E _ _).2.2]; ring)
        (by intro E j
            rw [abs_div,abs_of_pos (hu r j)]
            apply (div_le_iff₀ (hu r j)).mpr
            simpa only [rawUnitEntry_coordinate] using (S.global_bounds hB E j (j+r.val+1)).2.2)))

theorem globalX_zero (S : RelativeLDUData l d u) (E : FullBand p q) (i j : ℕ)
    (h : i ≤ j ∨ j+p < i) : S.globalX E i j=0 := by
  rcases h with h|h
  · exact (S.inv_triangular E (max i j+1)).1 ⟨i,by omega⟩ ⟨j,by omega⟩ h
  · exact (S.inv_bands E (max i j+1)).1 ⟨i,by omega⟩ ⟨j,by omega⟩ h
theorem globalY_zero (S : RelativeLDUData l d u) (E : FullBand p q) (i j : ℕ)
    (h : j ≤ i ∨ i+q < j) : S.globalY E i j=0 := by
  rcases h with h|h
  · exact (S.inv_triangular E (max i j+1)).2.2 ⟨i,by omega⟩ ⟨j,by omega⟩ h
  · exact (S.inv_bands E (max i j+1)).2 ⟨i,by omega⟩ ⟨j,by omega⟩ h

theorem inverseMap_lower_entry (S : RelativeLDUData l d u)
    (hl : ∀ i j,0<l i j) (hd : ∀ j,0<d j) (hu : ∀ i j,0<u i j)
    (C : ℝ) (hB : S.Bounds C) (E : FullBand p q) (i j : ℕ) :
    rawUnitEntry l i j*bandEntry (S.inverseMap hl hd hu C hB E).1 i j=S.globalX E i j := by
  by_cases hh : j < i ∧ i ≤ j+p
  · let r : Fin p := ⟨i-j-1,by omega⟩
    have hi : i=j+r.val+1 := by dsimp [r]; omega
    rw [hi,rawUnitEntry_coordinate,bandEntry_coordinate]
    change l r j*(S.globalX E (j+r.val+1) j/l r j)=S.globalX E (j+r.val+1) j
    field_simp [ne_of_gt (hl r j)]
  · simp only [bandEntry,dite_eq_right hh,mul_zero]
    exact (S.globalX_zero E i j (by omega)).symm

theorem inverseMap_upper_entry (S : RelativeLDUData l d u)
    (hl : ∀ i j,0<l i j) (hd : ∀ j,0<d j) (hu : ∀ i j,0<u i j)
    (C : ℝ) (hB : S.Bounds C) (E : FullBand p q) (i j : ℕ) :
    rawUnitEntry u j i*bandEntry (S.inverseMap hl hd hu C hB E).2.2 j i=S.globalY E i j := by
  by_cases hh : i < j ∧ j ≤ i+q
  · let r : Fin q := ⟨j-i-1,by omega⟩
    have hj : j=i+r.val+1 := by dsimp [r]; omega
    rw [hj,rawUnitEntry_coordinate,bandEntry_coordinate]
    change u r i*(S.globalY E i (i+r.val+1)/u r i)=S.globalY E i (i+r.val+1)
    field_simp [ne_of_gt (hu r i)]
  · simp only [bandEntry,dite_eq_right hh,mul_zero]
    exact (S.globalY_zero E i j (by omega)).symm

theorem inverseMap_diagonal_entry (S : RelativeLDUData l d u)
    (hl : ∀ i j,0<l i j) (hd : ∀ j,0<d j) (hu : ∀ i j,0<u i j)
    (C : ℝ) (hB : S.Bounds C) (E : FullBand p q) (i : ℕ) :
    d i*(S.inverseMap hl hd hu C hB E).2.1 i=S.globalZ E i i := by
  change d i*(S.globalZ E i i/d i)=_
  field_simp [ne_of_gt (hd i)]

theorem inverseMap_sections (S : RelativeLDUData l d u)
    (hl : ∀ i j,0<l i j) (hd : ∀ j,0<d j) (hu : ∀ i j,0<u i j)
    (C : ℝ) (hB : S.Bounds C) (E : FullBand p q) (N : ℕ) :
    (fun i j : Fin N=>rawUnitEntry l i.val j.val*
      bandEntry (S.inverseMap hl hd hu C hB E).1 i.val j.val)=S.invX E N ∧
    Matrix.diagonal (fun i : Fin N=>d i.val*(S.inverseMap hl hd hu C hB E).2.1 i.val)=S.invZ E N ∧
    (fun i j : Fin N=>rawUnitEntry u j.val i.val*
      bandEntry (S.inverseMap hl hd hu C hB E).2.2 j.val i.val)=S.invY E N := by
  refine ⟨?_,?_,?_⟩
  · ext i j
    rw [S.inverseMap_lower_entry]
    exact (S.global_section E N i j).1
  · ext i j
    by_cases he : i=j
    · subst j
      simp only [Matrix.diagonal_apply_eq,S.inverseMap_diagonal_entry]
      exact (S.global_section E N i i).2.1
    · rw [Matrix.diagonal_apply_ne _ he]
      exact ((S.inv_triangular E N).2.1 i j he).symm
  · ext i j
    rw [S.inverseMap_upper_entry]
    exact (S.global_section E N i j).2.2

theorem inverseMap_forcing_right (S : RelativeLDUData l d u)
    (hl : ∀ i j,0<l i j) (hd : ∀ j,0<d j) (hu : ∀ i j,0<u i j)
    (C : ℝ) (hB : S.Bounds C) (E : FullBand p q) (N : ℕ) :
    S.forcing (relativeLDUProductDerivative l d u hl hd hu 0 (S.inverseMap hl hd hu C hB E)) N=
      S.forcing E N := by
  have he := relativeLDUProductDerivative_section l d u hl hd hu (S.inverseMap hl hd hu C hB E) N
  have hp := S.inverseMap_sections hl hd hu C hB E N
  rw [hp.1,hp.2.1,hp.2.2,←S.lower_eq,←S.upper_eq,S.inv_eq] at he
  exact he

theorem inverseMap_right (S : RelativeLDUData l d u)
    (hl : ∀ i j,0<l i j) (hd : ∀ j,0<d j) (hu : ∀ i j,0<u i j)
    (C : ℝ) (hB : S.Bounds C) (E : FullBand p q) :
    relativeLDUProductDerivative l d u hl hd hu 0 (S.inverseMap hl hd hu C hB E)=E := by
  have entry (i j : ℕ) : rawFullEntry l d u i j*
      fullEntry (relativeLDUProductDerivative l d u hl hd hu 0 (S.inverseMap hl hd hu C hB E)) i j =
      rawFullEntry l d u i j*fullEntry E i j := by
    have he := S.inverseMap_forcing_right hl hd hu C hB E (max i j+1)
    exact congrArg (fun M : Mat (max i j+1)=>M ⟨i,by omega⟩ ⟨j,by omega⟩) he
  apply Prod.ext
  · funext r
    apply BoundedContinuousFunction.ext
    intro j
    have he := entry (j+r.val+1) j
    rw [fullEntry_lower,fullEntry_lower] at he
    have hp : 0<rawFullEntry l d u (j+r.val+1) j := by
      rw [show j+r.val+1=j+(r.val+1) by omega,rawFullEntry_lower]
      exact rawLDUSum_pos l d u hl hd hu _ _ _ _ (by omega) (by omega) (by omega)
    exact (mul_left_cancel₀ (ne_of_gt hp)) he
  · apply Prod.ext
    · apply BoundedContinuousFunction.ext
      intro j
      have he := entry j j
      rw [fullEntry_diag,fullEntry_diag] at he
      have hp : 0<rawFullEntry l d u j j := by
        have hh := rawFullEntry_lower l d u 0 j
        simp only [Nat.add_zero] at hh
        rw [hh]
        exact rawLDUSum_pos l d u hl hd hu _ _ _ _ (by omega) (by omega) (by omega)
      exact (mul_left_cancel₀ (ne_of_gt hp)) he
    · funext r
      apply BoundedContinuousFunction.ext
      intro j
      have he := entry j (j+r.val+1)
      rw [fullEntry_upper,fullEntry_upper] at he
      have hp : 0<rawFullEntry l d u j (j+r.val+1) := by
        rw [show j+r.val+1=j+(r.val+1) by omega,rawFullEntry_upper]
        exact rawLDUSum_pos l d u hl hd hu _ _ _ _ (by omega) (by omega) (by omega)
      exact (mul_left_cancel₀ (ne_of_gt hp)) he

theorem analyticSection_of_bounds (S : RelativeLDUData l d u)
    (hl : ∀ i j,0<l i j) (hd : ∀ j,0<d j) (hu : ∀ i j,0<u i j)
    (C : ℝ) (hB : S.Bounds C) : RelativeAnalyticLDUSection l d u hl hd hu := by
  apply relative_analytic_ldu_of_right_inverse l d u hl hd hu (S.inverseMap hl hd hu C hB)
  apply ContinuousLinearMap.ext
  exact S.inverseMap_right hl hd hu C hB

/-- Finite triangular uniqueness proves injectivity before any uniform
estimate for the formal inverse is available. -/
theorem derivative_injective (S : RelativeLDUData l d u)
    (hl : ∀ i j,0<l i j) (hd : ∀ j,0<d j) (hu : ∀ i j,0<u i j) :
    Function.Injective (relativeLDUProductDerivative l d u hl hd hu 0) := by
  have recover (E : FullBand p q) (N : ℕ) :
      (fun i j : Fin N=>rawUnitEntry l i.val j.val*bandEntry E.1 i.val j.val)=
        S.invX (relativeLDUProductDerivative l d u hl hd hu 0 E) N ∧
      Matrix.diagonal (fun i : Fin N=>d i.val*E.2.1 i.val)=
        S.invZ (relativeLDUProductDerivative l d u hl hd hu 0 E) N ∧
      (fun i j : Fin N=>rawUnitEntry u j.val i.val*bandEntry E.2.2 j.val i.val)=
        S.invY (relativeLDUProductDerivative l d u hl hd hu 0 E) N := by
    have he := relativeLDUProductDerivative_section l d u hl hd hu E N
    rw [←S.lower_eq,←S.upper_eq] at he
    have hx : StrictLower (fun i j : Fin N=>rawUnitEntry l i.val j.val*
        bandEntry E.1 i.val j.val) := by
      intro i j hij
      simp only [bandEntry_upper E.1 hij,mul_zero]
    have hz : Diag (Matrix.diagonal (fun i : Fin N=>d i.val*E.2.1 i.val)) := by
      intro i j hij
      exact Matrix.diagonal_apply_ne _ hij
    have hy : StrictUpper (fun i j : Fin N=>rawUnitEntry u j.val i.val*
        bandEntry E.2.2 j.val i.val) := by
      intro i j hij
      simp only [bandEntry_upper E.2.2 hij,mul_zero]
    have hrec := variation_unique (S.s.L N) (S.s.Li N) (S.s.U N) (S.s.Ui N)
      _ _ _ (fun i=>d i.val) (S.s.Li_L N) (S.s.L_Li N) (S.s.U_Ui N) (S.s.Ui_U N)
      (fun i=>ne_of_gt (hd i.val)) (S.s.lower_Li N) (S.s.upper_Ui N) hx hz hy
    dsimp only at hrec
    rw [←he] at hrec
    exact hrec
  intro E F hEF
  have hsec (N : ℕ) := recover E N
  have hsecF (N : ℕ) := recover F N
  apply Prod.ext
  · funext r
    apply BoundedContinuousFunction.ext
    intro j
    let N := j+r.val+2
    let i : Fin N := ⟨j+r.val+1,by dsimp [N]; omega⟩
    let k : Fin N := ⟨j,by dsimp [N]; omega⟩
    have hh := (hsec N).1.trans ((hEF ▸ (hsecF N).1).symm)
    have hval := congrArg (fun M : Mat N=>M i k) hh
    simp only [i,k,rawUnitEntry_coordinate,bandEntry_coordinate] at hval
    exact mul_left_cancel₀ (ne_of_gt (hl r j)) hval
  · apply Prod.ext
    · apply BoundedContinuousFunction.ext
      intro j
      let i : Fin (j+1) := ⟨j,by omega⟩
      have hh := (hsec (j+1)).2.1.trans ((hEF ▸ (hsecF (j+1)).2.1).symm)
      have hval := congrArg (fun M : Mat (j+1)=>M i i) hh
      simp only [Matrix.diagonal_apply_eq,i] at hval
      exact mul_left_cancel₀ (ne_of_gt (hd j)) hval
    · funext r
      apply BoundedContinuousFunction.ext
      intro j
      let N := j+r.val+2
      let i : Fin N := ⟨j+r.val+1,by dsimp [N]; omega⟩
      let k : Fin N := ⟨j,by dsimp [N]; omega⟩
      have hh := (hsec N).2.2.trans ((hEF ▸ (hsecF N).2.2).symm)
      have hval := congrArg (fun M : Mat N=>M k i) hh
      simp only [i,k,rawUnitEntry_coordinate,bandEntry_coordinate] at hval
      exact mul_left_cancel₀ (ne_of_gt (hu r j)) hval

#print axioms analyticSection_of_bounds
#print axioms derivative_injective

end RelativeLDUData
end BTP.RelativeStability
