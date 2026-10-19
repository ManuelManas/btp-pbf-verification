import FiniteLDUCompatibility

/-! Passage from compatible finite triangular solves to a bounded inverse
on the Banach space of all matrices in the prescribed band. -/
noncomputable section
open Matrix Finset
open BTP.GeneralStability
namespace BTP.Stability.BandLDU

theorem lowerPart_add {N : ℕ} (V W : Mat N) :
    lowerPart (V+W)=lowerPart V+lowerPart W := by
  ext i j
  simp only [lowerPart, Matrix.add_apply]
  split_ifs <;> simp

theorem upperPart_add {N : ℕ} (V W : Mat N) :
    upperPart (V+W)=upperPart V+upperPart W := by
  ext i j
  simp only [upperPart, Matrix.add_apply]
  split_ifs <;> simp

theorem diagPart_add {N : ℕ} (V W : Mat N) :
    diagPart (V+W)=diagPart V+diagPart W := by
  ext i j
  by_cases h : i=j
  · subst j; simp [diagPart]
  · simp [diagPart, Matrix.diagonal, h]

theorem lowerPart_smul {N : ℕ} (c : ℝ) (V : Mat N) :
    lowerPart (c • V)=c • lowerPart V := by
  ext i j
  simp only [lowerPart, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp

theorem upperPart_smul {N : ℕ} (c : ℝ) (V : Mat N) :
    upperPart (c • V)=c • upperPart V := by
  ext i j
  simp only [upperPart, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp

theorem diagPart_smul {N : ℕ} (c : ℝ) (V : Mat N) :
    diagPart (c • V)=c • diagPart V := by
  ext i j
  by_cases h : i=j
  · subst j; simp [diagPart]
  · simp [diagPart, Matrix.diagonal, h]

@[simp] theorem fullSection_add {p q N : ℕ} (E F : FullBand p q) :
    fullSection (E+F) N = fullSection E N + fullSection F N := by
  ext i j
  exact fullEntry_add _ _ _ _

@[simp] theorem fullSection_smul {p q N : ℕ} (c : ℝ) (E : FullBand p q) :
    fullSection (c • E) N = c • fullSection E N := by
  ext i j
  exact fullEntry_smul _ _ _ _

namespace SectionData

def invSum (s : SectionData) {p q : ℕ} (E : FullBand p q) (N : ℕ) : Mat N :=
  s.invX E N + s.invZ E N + s.invY E N

theorem invSum_coherent (s : SectionData) {p q : ℕ} (E : FullBand p q) (N : ℕ) :
    principal (s.invSum E (N+1))=s.invSum E N := by
  dsimp [invSum]
  rw [(s.inv_coherent E N).1,
    (s.inv_coherent E N).2.1, (s.inv_coherent E N).2.2]

theorem invSum_add (s : SectionData) {p q : ℕ} (E F : FullBand p q) (N : ℕ) :
    s.invSum (E+F) N=s.invSum E N+s.invSum F N := by
  simp only [invSum, invX, invY, invZ, invV, fullSection_add, Matrix.mul_add,
    Matrix.add_mul, lowerPart_add, upperPart_add, diagPart_add]
  abel

theorem invSum_smul (s : SectionData) {p q : ℕ} (c : ℝ) (E : FullBand p q) (N : ℕ) :
    s.invSum (c • E) N=c • s.invSum E N := by
  simp only [invSum, invX, invY, invZ, invV, fullSection_smul, Matrix.mul_smul,
    Matrix.smul_mul, lowerPart_smul, upperPart_smul, diagPart_smul, smul_add]

def globalInv (s : SectionData) {p q : ℕ} (E : FullBand p q) : ℕ → ℕ → ℝ :=
  coherentEntry (s.invSum E)

theorem globalInv_section (s : SectionData) {p q : ℕ} (E : FullBand p q)
    (N : ℕ) (i j : Fin N) : s.globalInv E i.val j.val=s.invSum E N i j :=
  coherentEntry_section _ (s.invSum_coherent E) N i j

theorem globalInv_add (s : SectionData) {p q : ℕ} (E F : FullBand p q) (i j : ℕ) :
    s.globalInv (E+F) i j=s.globalInv E i j+s.globalInv F i j := by
  dsimp [globalInv, coherentEntry]
  rw [s.invSum_add]
  rfl

theorem globalInv_smul (s : SectionData) {p q : ℕ} (c : ℝ) (E : FullBand p q) (i j : ℕ) :
    s.globalInv (c • E) i j=c*s.globalInv E i j := by
  dsimp [globalInv, coherentEntry]
  rw [s.invSum_smul]
  rfl

theorem inv_bands (s : SectionData) {p q : ℕ}
    (hL : ∀ N, LowerBandwidth p (s.L N)) (hU : ∀ N, UpperBandwidth q (s.U N))
    (E : FullBand p q) (N : ℕ) :
    LowerBandwidth p (s.invX E N) ∧ UpperBandwidth q (s.invY E N) :=
  variation_formula_bands _ _ _ _ _ _ p q (s.L_Li N) (s.Ui_U N)
    (hL N) (hU N) (s.lower_Li N) (s.upper_Ui N) (fullSection_lower_band E) (fullSection_upper_band E)

theorem globalInv_band (s : SectionData) {p q : ℕ}
    (hL : ∀ N, LowerBandwidth p (s.L N)) (hU : ∀ N, UpperBandwidth q (s.U N))
    (E : FullBand p q) (i j : ℕ) (h : j+p < i ∨ i+q < j) : s.globalInv E i j=0 := by
  let N := max i j+1
  let ii : Fin N := ⟨i, by dsimp [N]; omega⟩
  let jj : Fin N := ⟨j, by dsimp [N]; omega⟩
  change s.invSum E N ii jj=0
  have ht := s.inv_triangular E N
  have hb := s.inv_bands hL hU E N
  rcases h with h | h
  · have hx := hb.1 ii jj h
    have hz := ht.2.1 ii jj (by intro hij; have := congrArg Fin.val hij; dsimp [ii,jj] at this; omega)
    have hy := ht.2.2 ii jj (by change j ≤ i; omega)
    simp [invSum, hx, hz, hy]
  · have hx := ht.1 ii jj (by change i ≤ j; omega)
    have hz := ht.2.1 ii jj (by intro hij; have := congrArg Fin.val hij; dsimp [ii,jj] at this; omega)
    have hy := hb.2 ii jj h
    simp [invSum, hx, hz, hy]

theorem globalInv_bound (s : SectionData) {p q : ℕ} {C : ℝ}
    (hX : ∀ (E : FullBand p q) N i j, |s.invX E N i j|≤C*‖E‖)
    (hZ : ∀ (E : FullBand p q) N i j, |s.invZ E N i j|≤C*‖E‖)
    (hY : ∀ (E : FullBand p q) N i j, |s.invY E N i j|≤C*‖E‖)
    (E : FullBand p q) (i j : ℕ) : |s.globalInv E i j|≤(3*C)*‖E‖ := by
  dsimp [globalInv, coherentEntry, invSum]
  have hx := hX E (max i j+1) ⟨i,by omega⟩ ⟨j,by omega⟩
  have hz := hZ E (max i j+1) ⟨i,by omega⟩ ⟨j,by omega⟩
  have hy := hY E (max i j+1) ⟨i,by omega⟩ ⟨j,by omega⟩
  calc
    _ ≤ |s.invX E _ _ _|+|s.invZ E _ _ _|+|s.invY E _ _ _| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ C*‖E‖+C*‖E‖+C*‖E‖ := add_le_add (add_le_add hx hz) hy
    _ = (3*C)*‖E‖ := by ring

def inverseMap (s : SectionData) {p q : ℕ}
    (hL : ∀ N, LowerBandwidth p (s.L N)) (hU : ∀ N, UpperBandwidth q (s.U N))
    (C : ℝ)
    (hX : ∀ (E : FullBand p q) N i j, |s.invX E N i j|≤C*‖E‖)
    (hZ : ∀ (E : FullBand p q) N i j, |s.invZ E N i j|≤C*‖E‖)
    (hY : ∀ (E : FullBand p q) N i j, |s.invY E N i j|≤C*‖E‖) :
    FullBand p q →L[ℝ] FullBand p q :=
  let B : FullBand p q →ₗ[ℝ] FullBand p q :=
    { toFun := fun E => fullOfEntries (s.globalInv E) ((3*C)*‖E‖)
        (s.globalInv_bound hX hZ hY E)
      map_add' := by
        intro E F
        apply fullEntry_ext
        intro i j
        rw [fullEntry_add]
        simp only [fullOfEntries_entry _ _ _ (s.globalInv_band hL hU _)]
        exact s.globalInv_add E F i j
      map_smul' := by
        intro c E
        apply fullEntry_ext
        intro i j
        rw [fullEntry_smul]
        simp only [fullOfEntries_entry _ _ _ (s.globalInv_band hL hU _)]
        exact s.globalInv_smul c E i j }
  B.mkContinuous (3*C) (fun E => norm_fullOfEntries_le _ _ _)

theorem inverseMap_section (s : SectionData) {p q : ℕ}
    (hL : ∀ N, LowerBandwidth p (s.L N)) (hU : ∀ N, UpperBandwidth q (s.U N))
    (C : ℝ)
    (hX : ∀ (E : FullBand p q) N i j, |s.invX E N i j|≤C*‖E‖)
    (hZ : ∀ (E : FullBand p q) N i j, |s.invZ E N i j|≤C*‖E‖)
    (hY : ∀ (E : FullBand p q) N i j, |s.invY E N i j|≤C*‖E‖)
    (E : FullBand p q) (N : ℕ) :
    fullSection (s.inverseMap hL hU C hX hZ hY E) N=s.invSum E N := by
  ext i j
  change fullEntry (fullOfEntries (s.globalInv E) _ _) i.val j.val = _
  rw [fullOfEntries_entry _ _ _ (s.globalInv_band hL hU E)]
  exact s.globalInv_section E N i j

/-- The meaning of the LDU derivative in the full-band coordinates. This
is an entrywise finite-section identity, not an invertibility hypothesis. -/
def IsDerivative (s : SectionData) {p q : ℕ} (A : FullBand p q →L[ℝ] FullBand p q) : Prop :=
  ∀ E N, fullSection (A E) N =
    variation (s.L N) (Matrix.diagonal (fun i => s.d i.val)) (s.U N)
      (lowerPart (fullSection E N)) (diagPart (fullSection E N))
      (upperPart (fullSection E N))

theorem inverseMap_right (s : SectionData) {p q : ℕ}
    (hL : ∀ N, LowerBandwidth p (s.L N)) (hU : ∀ N, UpperBandwidth q (s.U N))
    (C : ℝ)
    (hX : ∀ (E : FullBand p q) N i j, |s.invX E N i j|≤C*‖E‖)
    (hZ : ∀ (E : FullBand p q) N i j, |s.invZ E N i j|≤C*‖E‖)
    (hY : ∀ (E : FullBand p q) N i j, |s.invY E N i j|≤C*‖E‖)
    (A : FullBand p q →L[ℝ] FullBand p q) (hA : s.IsDerivative A)
    (E : FullBand p q) : A (s.inverseMap hL hU C hX hZ hY E)=E := by
  apply fullEntry_ext
  intro i j
  let N := max i j+1
  let ii : Fin N := ⟨i, by dsimp [N]; omega⟩
  let jj : Fin N := ⟨j, by dsimp [N]; omega⟩
  have he := hA (s.inverseMap hL hU C hX hZ hY E) N
  rw [s.inverseMap_section] at he
  have ht := s.inv_triangular E N
  have hp := parts_unique ht.1 ht.2.1 ht.2.2 (show s.invSum E N=s.invSum E N from rfl)
  rw [← hp.1, ← hp.2.1, ← hp.2.2, s.inv_eq] at he
  exact congrArg (fun M : Mat N => M ii jj) he

theorem inverseMap_left (s : SectionData) {p q : ℕ}
    (hL : ∀ N, LowerBandwidth p (s.L N)) (hU : ∀ N, UpperBandwidth q (s.U N))
    (C : ℝ)
    (hX : ∀ (E : FullBand p q) N i j, |s.invX E N i j|≤C*‖E‖)
    (hZ : ∀ (E : FullBand p q) N i j, |s.invZ E N i j|≤C*‖E‖)
    (hY : ∀ (E : FullBand p q) N i j, |s.invY E N i j|≤C*‖E‖)
    (A : FullBand p q →L[ℝ] FullBand p q) (hA : s.IsDerivative A)
    (E : FullBand p q) : s.inverseMap hL hU C hX hZ hY (A E)=E := by
  apply fullEntry_ext
  intro i j
  let N := max i j+1
  let ii : Fin N := ⟨i, by dsimp [N]; omega⟩
  let jj : Fin N := ⟨j, by dsimp [N]; omega⟩
  have hu := variation_unique (s.L N) (s.Li N) (s.U N) (s.Ui N)
    (lowerPart (fullSection E N)) (diagPart (fullSection E N))
    (upperPart (fullSection E N)) (fun k => s.d k.val)
    (s.Li_L N) (s.L_Li N) (s.U_Ui N) (s.Ui_U N) (fun k => s.d_ne k.val)
    (s.lower_Li N) (s.upper_Ui N) (lowerPart_strict _) (diagPart_diag _) (upperPart_strict _)
  dsimp only at hu
  rw [← hA E N] at hu
  have he : s.invSum (A E) N = fullSection E N := by
    change s.invX (A E) N + s.invZ (A E) N + s.invY (A E) N = _
    dsimp only [invX, invY, invZ, invV]
    rw [← hu.1, ← hu.2.1, ← hu.2.2, parts_sum]
  have hr := s.inverseMap_section hL hU C hX hZ hY (A E) N
  rw [he] at hr
  exact congrArg (fun M : Mat N => M ii jj) hr

/-- The bounded inverse on the full band is assembled from the actual
finite-section formulas. No inverse or surjectivity of A is assumed. -/
def derivativeEquiv (s : SectionData) {p q : ℕ}
    (hL : ∀ N, LowerBandwidth p (s.L N)) (hU : ∀ N, UpperBandwidth q (s.U N))
    (C : ℝ)
    (hX : ∀ (E : FullBand p q) N i j, |s.invX E N i j|≤C*‖E‖)
    (hZ : ∀ (E : FullBand p q) N i j, |s.invZ E N i j|≤C*‖E‖)
    (hY : ∀ (E : FullBand p q) N i j, |s.invY E N i j|≤C*‖E‖)
    (A : FullBand p q →L[ℝ] FullBand p q) (hA : s.IsDerivative A) :
    FullBand p q ≃L[ℝ] FullBand p q :=
  ContinuousLinearEquiv.equivOfInverse A (s.inverseMap hL hU C hX hZ hY)
    (s.inverseMap_left hL hU C hX hZ hY A hA)
    (s.inverseMap_right hL hU C hX hZ hY A hA)

@[simp] theorem derivativeEquiv_apply (s : SectionData) {p q : ℕ}
    (hL : ∀ N, LowerBandwidth p (s.L N)) (hU : ∀ N, UpperBandwidth q (s.U N))
    (C : ℝ)
    (hX : ∀ (E : FullBand p q) N i j, |s.invX E N i j|≤C*‖E‖)
    (hZ : ∀ (E : FullBand p q) N i j, |s.invZ E N i j|≤C*‖E‖)
    (hY : ∀ (E : FullBand p q) N i j, |s.invY E N i j|≤C*‖E‖)
    (A : FullBand p q →L[ℝ] FullBand p q) (hA : s.IsDerivative A)
    (E : FullBand p q) : s.derivativeEquiv hL hU C hX hZ hY A hA E=A E := rfl

end SectionData
#print axioms SectionData.derivativeEquiv
end BTP.Stability.BandLDU
