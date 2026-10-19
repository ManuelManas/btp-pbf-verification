import AnalyticLDUDerivative

noncomputable section
set_option maxHeartbeats 800000
open scoped BigOperators
namespace BTP.GeneralStability

theorem unitBandEntry_coefficient {m : ℕ} (G : LowerBand m) (i j : ℕ) :
    unitBandEntry G i j = if j ≤ i then bandCoefficient G (i-j) j else 0 := by
  by_cases he : i=j
  · subst i
    simp [unitBandEntry]
  · by_cases hji : j < i
    · by_cases hb : i ≤ j+m
      · have hr : i-j-1 < m := by omega
        have hd : i-j-1+1=i-j := by omega
        have hc := congrArg (fun f : Seq => f j) (bandCoefficient_coordinate G ⟨i-j-1,hr⟩)
        dsimp only at hc
        rw [hd] at hc
        simp only [unitBandEntry,he,↓reduceIte,bandEntry,hji,hb,and_self,↓reduceDIte,
          Nat.le_of_lt hji]
        exact hc.symm
      · simp [unitBandEntry,he,bandEntry,hb,Nat.le_of_lt hji,
          bandCoefficient_outside G (i-j) (by omega)]
    · have hnot : ¬j ≤ i := by omega
      simp [unitBandEntry,he,bandEntry,hji,hnot]

theorem two_truncations (F : ℕ → ℝ) (j q : ℕ) :
    (∑ t ∈ Finset.range (q+1), if t ≤ j then F t else 0) =
      ∑ t ∈ Finset.range (j+1), if t ≤ q then F t else 0 := by
  classical
  rw [←Finset.sum_filter,←Finset.sum_filter]
  congr 1
  ext t
  simp only [Finset.mem_filter,Finset.mem_range]
  omega

theorem reverseWindowSum (F : ℕ → ℝ) (j q : ℕ) :
    (∑ t ∈ Finset.range (q+1), if t ≤ j then F (j-t) else 0) =
      ∑ k ∈ Finset.range (j+1), if j-k ≤ q then F k else 0 := by
  rw [two_truncations]
  conv_rhs => rw [←Finset.sum_range_reflect (fun k => if j-k ≤ q then F k else 0) (j+1)]
  apply Finset.sum_congr rfl
  intro t ht
  have ht' : t ≤ j := by simpa using ht
  have hsub : j+1-1-t=j-t := by omega
  have hcancel : j-(j-t)=t := by omega
  simp only [hsub,hcancel]

theorem lduLowerCoefficient_entry {p q : ℕ} (x : FullBand p q) (d j : ℕ) :
    lduLowerCoefficient x d j =
      ∑ k ∈ Finset.range (j+1),
        unitBandEntry x.1 (j+d) k * x.2.1 k * unitBandEntry x.2.2 j k := by
  let F : ℕ → ℝ := fun k => unitBandEntry x.1 (j+d) k * x.2.1 k * unitBandEntry x.2.2 j k
  have hleft : lduLowerCoefficient x d j =
      ∑ t ∈ Finset.range (q+1), if t ≤ j then F (j-t) else 0 := by
    unfold lduLowerCoefficient
    rw [BoundedContinuousFunction.sum_apply]
    apply Finset.sum_congr rfl
    intro t _
    rw [zeroExtension_apply]
    unfold initialExtension
    split_ifs with ht
    · dsimp [F]
      have hL : j+d-(j-t)=d+t := by omega
      have hU : j-(j-t)=t := by omega
      simp only [unitBandEntry_coefficient,
        show j-t≤j+d by omega,show j-t≤j by omega,↓reduceIte,hL,hU]
    · rfl
  rw [hleft,reverseWindowSum]
  apply Finset.sum_congr rfl
  intro k hk
  split_ifs with hq
  · rfl
  · have hk' : k ≤ j := by simpa using hk
    have hout : q < j-k := by omega
    simp [unitBandEntry_coefficient,hk',bandCoefficient_outside x.2.2 (j-k) hout]

theorem lduUpperCoefficient_entry {p q : ℕ} (x : FullBand p q) (d j : ℕ) :
    lduUpperCoefficient x d j =
      ∑ k ∈ Finset.range (j+1),
        unitBandEntry x.1 j k * x.2.1 k * unitBandEntry x.2.2 (j+d) k := by
  have hs : lduUpperCoefficient x d = lduLowerCoefficient (x.2.2, (x.2.1,x.1)) d := by
    unfold lduUpperCoefficient lduLowerCoefficient
    apply Finset.sum_congr rfl
    intro t _
    congr 1
    ring
  rw [hs,lduLowerCoefficient_entry]
  apply Finset.sum_congr rfl
  intro k _
  dsimp
  ring

theorem lduLowerCoefficient_outside {p q : ℕ} (x : FullBand p q) (d : ℕ) (hd : p<d) :
    lduLowerCoefficient x d = 0 := by
  unfold lduLowerCoefficient
  apply Finset.sum_eq_zero
  intro t _
  rw [bandCoefficient_outside x.1 (d+t) (by omega)]
  simp

theorem lduUpperCoefficient_outside {p q : ℕ} (x : FullBand p q) (d : ℕ) (hd : q<d) :
    lduUpperCoefficient x d = 0 := by
  unfold lduUpperCoefficient
  apply Finset.sum_eq_zero
  intro t _
  rw [bandCoefficient_outside x.2.2 (d+t) (by omega)]
  simp

theorem lduProduct_entry {p q : ℕ} (x : FullBand p q) (i j : ℕ) :
    fullEntry (lduProduct x) i j =
      ∑ k ∈ Finset.range (min i j+1),
        unitBandEntry x.1 i k * x.2.1 k * unitBandEntry x.2.2 j k := by
  by_cases he : i=j
  · subst j
    simpa [lduProduct] using lduLowerCoefficient_entry x 0 i
  · by_cases hj : j < i
    · have hm : min i j=j := min_eq_right (Nat.le_of_lt hj)
      rw [hm]
      have hs : j+(i-j)=i := by omega
      calc
        _ = lduLowerCoefficient x (i-j) j := by
          by_cases hb : i ≤ j+p
          · simp [fullEntry,he,hj,bandEntry,hb,lduProduct,
              show i-j-1+1=i-j by omega]
          · simp [fullEntry,he,hj,bandEntry,hb,lduLowerCoefficient_outside x (i-j) (by omega)]
        _ = _ := by simpa only [hs] using lduLowerCoefficient_entry x (i-j) j
    · have hi : i < j := by omega
      have hm : min i j=i := min_eq_left (Nat.le_of_lt hi)
      rw [hm]
      have hs : i+(j-i)=j := by omega
      calc
        _ = lduUpperCoefficient x (j-i) i := by
          by_cases hb : j ≤ i+q
          · simp [fullEntry,he,hj,hi,bandEntry,hb,lduProduct,
              show j-i-1+1=j-i by omega]
          · simp [fullEntry,he,hj,hi,bandEntry,hb,lduUpperCoefficient_outside x (j-i) (by omega)]
        _ = _ := by simpa only [hs] using lduUpperCoefficient_entry x (j-i) i

theorem lduProduct_entry_fin {p q N : ℕ} (x : FullBand p q) (i j : Fin N) :
    fullEntry (lduProduct x) i.val j.val =
      ∑ k : Fin N, unitBandEntry x.1 i.val k.val * x.2.1 k.val *
        unitBandEntry x.2.2 j.val k.val := by
  rw [lduProduct_entry,Fin.sum_univ_eq_sum_range
    (fun k => unitBandEntry x.1 i.val k * x.2.1 k * unitBandEntry x.2.2 j.val k)]
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro k _ hk
  have hk' : min i.val j.val < k := by
    simp only [Finset.mem_range] at hk
    omega
  rcases lt_or_ge i.val j.val with hij|hij
  · have hik : ¬k ≤ i.val := by omega
    simp [unitBandEntry_coefficient,hik]
  · have hjk : ¬k ≤ j.val := by omega
    simp [unitBandEntry_coefficient,hjk]

theorem finiteLower_entry {p q N : ℕ} (x : FullBand p q) (i j : Fin N) :
    (1 + BTP.Stability.BandLDU.lowerPart (fullSection x N)) i j =
      unitBandEntry x.1 i.val j.val := by
  by_cases he : i=j
  · subst j
    simp [unitBandEntry,BTP.Stability.BandLDU.lowerPart]
  · have hne : i.val≠j.val := fun h => he (Fin.ext h)
    by_cases hj : j < i
    · simp [unitBandEntry,BTP.Stability.BandLDU.lowerPart,he,hj,fullSection,fullEntry,hne]
    · have hb : bandEntry x.1 i.val j.val=0 := by
        unfold bandEntry
        simp [show ¬j.val < i.val from hj]
      simp [unitBandEntry,BTP.Stability.BandLDU.lowerPart,he,hj,hne,hb]

theorem finiteUpper_entry {p q N : ℕ} (x : FullBand p q) (i j : Fin N) :
    (1 + BTP.Stability.BandLDU.upperPart (fullSection x N)) i j =
      unitBandEntry x.2.2 j.val i.val := by
  by_cases he : i=j
  · subst j
    simp [unitBandEntry,BTP.Stability.BandLDU.upperPart]
  · have hne : i.val≠j.val := fun h => he (Fin.ext h)
    by_cases hi : i < j
    · simp [unitBandEntry,BTP.Stability.BandLDU.upperPart,he,hi,fullSection,fullEntry,hne,
        Ne.symm hne,show ¬j.val < i.val by omega]
    · have hb : bandEntry x.2.2 j.val i.val=0 := by
        unfold bandEntry
        simp [show ¬i.val < j.val from hi]
      simp [unitBandEntry,BTP.Stability.BandLDU.upperPart,he,hi,Ne.symm hne,hb]

/-- Every leading finite section of the analytic coordinate product is
the ordinary matrix product of its normalized lower, diagonal and upper
factors. -/
theorem lduProduct_section {p q : ℕ} (x : FullBand p q) (N : ℕ) :
    fullSection (lduProduct x) N =
      (1 + BTP.Stability.BandLDU.lowerPart (fullSection x N)) *
      Matrix.diagonal (fun i : Fin N => x.2.1 i.val) *
      (1 + BTP.Stability.BandLDU.upperPart (fullSection x N)) := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal,finiteLower_entry,finiteUpper_entry]
  exact lduProduct_entry_fin x i j

#print axioms lduProduct_section

end BTP.GeneralStability
