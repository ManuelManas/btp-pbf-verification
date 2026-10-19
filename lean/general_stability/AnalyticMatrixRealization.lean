import AnalyticFactorization

noncomputable section
namespace BTP.GeneralStability

/-- The bounded coefficient product agrees with the row-coefficient
product formed by ordinary bidiagonal multiplication on the right. -/
theorem productCoefficient_eq_productCoefficients (b : ℕ → Seq) (k d j : ℕ) :
    productCoefficient (List.ofFn (fun i : Fin k => b i.val)) d j =
      productCoefficients (fun i n => b i n) k d (j+d) := by
  induction k generalizing d j with
  | zero =>
    cases d <;> simp [productCoefficient, productCoefficients]
  | succ k ih =>
    rw [List.ofFn_succ']
    cases d with
    | zero => simp
    | succ d =>
      simp only [List.concat_eq_append, Fin.val_castSucc, Fin.val_last]
      rw [productCoefficient_append, ih, ih]
      simp only [productCoefficients, rightBidiagonal]
      have hsub : j+(d+1)-d = j+1 := by omega
      rw [hsub]
      rw [show j+1+d = j+(d+1) by omega]

/-- Matrix entries of the Banach-space product coincide with the genuine
ordered product of lower bidiagonal matrices. -/
theorem lowerProductBand_matrix {p : ℕ} (a : Fin p → Seq) (i j : ℕ) :
    unitBandEntry (lowerProductBand a) i j =
      coefficientMatrix
        (productCoefficients (fun k n => if h : k < p then a ⟨k,h⟩ n else 0) p) i j := by
  let b : ℕ → Seq := fun k => if h : k < p then a ⟨k,h⟩ else 0
  have hb : (fun k n => b k n) =
      (fun k n => if h : k < p then a ⟨k,h⟩ n else 0) := by
    funext k n
    dsimp [b]
    split_ifs <;> rfl
  have ha : List.ofFn (fun k : Fin p => b k.val) = List.ofFn a := by
    congr 1
    funext k
    simp [b, k.isLt]
  by_cases hdiag : i=j
  · subst i
    simp [unitBandEntry, coefficientMatrix]
  · by_cases hji : j < i
    · by_cases hband : i ≤ j+p
      · simp only [unitBandEntry, hdiag, ↓reduceIte, bandEntry,
          hji, hband, and_self, ↓reduceDIte, lowerProductBand,
          coefficientMatrix, Nat.le_of_lt hji, ↓reduceIte]
        have hdiff : i-j-1+1 = i-j := by omega
        rw [hdiff, ←ha, productCoefficient_eq_productCoefficients, hb]
        congr 1
        omega
      · have hout : p < i-j := by omega
        simp [unitBandEntry, hdiag, bandEntry, hband, coefficientMatrix,
          Nat.le_of_lt hji, productCoefficients_band _ p _ _ hout]
    · have hnot : ¬j ≤ i := by omega
      simp [unitBandEntry, hdiag, bandEntry, hji, coefficientMatrix, hnot]

#print axioms productCoefficient_eq_productCoefficients
#print axioms lowerProductBand_matrix

end BTP.GeneralStability
