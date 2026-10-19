import FactorOrderBridge

noncomputable section
open scoped BigOperators
namespace BTP.Stability.BandLDU
open BTP BTP.GeneralStability

/-- Formal triangular uniqueness makes the normalized LDU derivative
injective even when its formal inverse is not bounded. -/
theorem SectionData.derivative_injective (s : SectionData) {p q : ℕ}
    (A : FullBand p q →L[ℝ] FullBand p q) (hA : s.IsDerivative A) :
    Function.Injective A := by
  have hrecover (E : FullBand p q) (N : ℕ) : s.invSum (A E) N=fullSection E N := by
    have hu := variation_unique (s.L N) (s.Li N) (s.U N) (s.Ui N)
      (lowerPart (fullSection E N)) (diagPart (fullSection E N))
      (upperPart (fullSection E N)) (fun k => s.d k.val)
      (s.Li_L N) (s.L_Li N) (s.U_Ui N) (s.Ui_U N) (fun k => s.d_ne k.val)
      (s.lower_Li N) (s.upper_Ui N) (lowerPart_strict _) (diagPart_diag _) (upperPart_strict _)
    dsimp only at hu
    rw [←hA E N] at hu
    change s.invX (A E) N+s.invZ (A E) N+s.invY (A E) N=_
    dsimp only [SectionData.invX,SectionData.invY,SectionData.invZ,SectionData.invV]
    rw [←hu.1,←hu.2.1,←hu.2.2,parts_sum]
  intro E F he
  apply fullEntry_ext
  intro i j
  let N := max i j+1
  let ii : Fin N := ⟨i,by dsimp [N]; omega⟩
  let jj : Fin N := ⟨j,by dsimp [N]; omega⟩
  have hsec : fullSection E N=fullSection F N := by
    rw [←hrecover E N,he,hrecover F N]
  exact congrArg (fun M : Mat N => M ii jj) hsec

theorem factorBase_derivative_injective {p q : ℕ}
    (a : Fin p → Seq) (d : Seq) (b : Fin q → Seq) (hd : ∀ n,d n≠0)
    {M : ℝ} (hM : 0≤M) (haM : ∀ i n,|a i n|≤M) (hbM : ∀ j n,|b j n|≤M) :
    Function.Injective (lduProductDerivative (factorBase a d b)) := by
  have ha : ∀ i<p,∀ n,0<n → |reversedEntries a i n|≤M := by
    intro i hi n _
    simp only [reversedEntries,hi,↓reduceDIte]
    exact haM _ _
  have hb : ∀ i<q,∀ n,0<n → |reversedEntries b i n|≤M := by
    intro i hi n _
    simp only [reversedEntries,hi,↓reduceDIte]
    exact hbM _ _
  have he := (actualData (reversedEntries a) (reversedEntries b) p q d hd).derivative_injective
    _ (actualBase_derivative (reversedEntries a) (reversedEntries b) p q d hd M hM ha hb)
  rw [reversed_factor_base] at he
  exact he

#print axioms SectionData.derivative_injective
#print axioms factorBase_derivative_injective
end BTP.Stability.BandLDU
