import RelativeLDUProduct
import AnalyticLDUDerivativeMatrix

noncomputable section
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace BTP.RelativeStability
open BTP.Stability BTP.GeneralStability

def rawUnitEntry {p : ℕ} (l : Fin p → ℕ → ℝ) (i j : ℕ) : ℝ :=
  if j ≤ i then rawTriangular l (i-j) j else 0

@[simp] theorem rawTriangular_outside {p : ℕ} (l : Fin p → ℕ → ℝ)
    (r j : ℕ) (hr : p < r) : rawTriangular l r j=0 := by
  simp [rawTriangular,show r≠0 by omega,not_le.mpr hr]

theorem rawLDUSum_lower {p q : ℕ} (l : Fin p → ℕ → ℝ) (d : ℕ → ℝ)
    (u : Fin q → ℕ → ℝ) (r j : ℕ) :
    rawLDUSum l d u r 0 (q+1) j =
      ∑ k ∈ Finset.range (j+1),rawUnitEntry l (j+r) k*d k*rawUnitEntry u j k := by
  let F : ℕ → ℝ := fun k => rawUnitEntry l (j+r) k*d k*rawUnitEntry u j k
  have he : rawLDUSum l d u r 0 (q+1) j =
      ∑ t ∈ Finset.range (q+1),if t ≤ j then F (j-t) else 0 := by
    apply Finset.sum_congr rfl
    intro t _
    unfold rawLDUTerm
    split_ifs with ht
    · simp [F,rawUnitEntry,show j-t ≤ j+r by omega,show j-t ≤ j by omega,
        show j+r-(j-t)=r+t by omega,show j-(j-t)=t by omega]
    · rfl
  rw [he,reverseWindowSum]
  apply Finset.sum_congr rfl
  intro k hk
  split_ifs with hq
  · rfl
  · have hk' : k ≤ j := by simpa using hk
    simp [rawUnitEntry,hk',rawTriangular_outside u (j-k) k (by omega)]

theorem rawLDUSum_upper {p q : ℕ} (l : Fin p → ℕ → ℝ) (d : ℕ → ℝ)
    (u : Fin q → ℕ → ℝ) (s j : ℕ) :
    rawLDUSum l d u 0 s (p+1) j =
      ∑ k ∈ Finset.range (j+1),rawUnitEntry l j k*d k*rawUnitEntry u (j+s) k := by
  have he : rawLDUSum l d u 0 s (p+1) j=rawLDUSum u d l s 0 (p+1) j := by
    apply Finset.sum_congr rfl
    intro t _
    unfold rawLDUTerm
    split_ifs <;> ring
  rw [he,rawLDUSum_lower]
  apply Finset.sum_congr rfl
  intro k _
  ring

def rawFullEntry {p q : ℕ} (l : Fin p → ℕ → ℝ) (d : ℕ → ℝ)
    (u : Fin q → ℕ → ℝ) (i j : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (min i j+1),rawUnitEntry l i k*d k*rawUnitEntry u j k

theorem rawFullEntry_fin {p q N : ℕ} (l : Fin p → ℕ → ℝ) (d : ℕ → ℝ)
    (u : Fin q → ℕ → ℝ) (i j : Fin N) :
    rawFullEntry l d u i.val j.val =
      ∑ k : Fin N,rawUnitEntry l i.val k.val*d k.val*rawUnitEntry u j.val k.val := by
  rw [rawFullEntry,Fin.sum_univ_eq_sum_range
    (fun k => rawUnitEntry l i.val k*d k*rawUnitEntry u j.val k)]
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro k _ hk
  have hk' : min i.val j.val < k := by
    simp only [Finset.mem_range] at hk
    omega
  rcases lt_or_ge i.val j.val with hij|hij
  · simp [rawUnitEntry,show ¬ k ≤ i.val by omega]
  · simp [rawUnitEntry,show ¬ k ≤ j.val by omega]

theorem rawFullEntry_lower {p q : ℕ} (l : Fin p → ℕ → ℝ) (d : ℕ → ℝ)
    (u : Fin q → ℕ → ℝ) (r j : ℕ) :
    rawFullEntry l d u (j+r) j=rawLDUSum l d u r 0 (q+1) j := by
  rw [rawLDUSum_lower,rawFullEntry,Nat.min_eq_right (by omega)]

theorem rawFullEntry_upper {p q : ℕ} (l : Fin p → ℕ → ℝ) (d : ℕ → ℝ)
    (u : Fin q → ℕ → ℝ) (s j : ℕ) :
    rawFullEntry l d u j (j+s)=rawLDUSum l d u 0 s (p+1) j := by
  rw [rawLDUSum_upper,rawFullEntry,Nat.min_eq_left (by omega)]

theorem rawUnitEntry_perturbed {p : ℕ} (l : Fin p → ℕ → ℝ)
    (h : LowerBand p) (t : ℝ) (i j : ℕ) :
    rawUnitEntry (fun r n => l r n*(1+t*h r n)) i j =
      rawUnitEntry l i j+t*(rawUnitEntry l i j*bandEntry h i j) := by
  by_cases he : i=j
  · subst j
    simp [rawUnitEntry,rawTriangular,bandEntry]
  · by_cases hji : j < i
    · by_cases hb : i ≤ j+p
      · have hr : i-j≠0 := by omega
        simp [rawUnitEntry,rawTriangular,bandEntry,hr,Nat.le_of_lt hji,
          show i-j ≤ p by omega,hji,hb]
        ring
      · simp [rawUnitEntry,rawTriangular,bandEntry,show i-j≠0 by omega,
          show ¬i-j ≤ p by omega,hb]
    · simp [rawUnitEntry,show ¬j ≤ i by omega]

theorem relativeLDUProduct_actual_entry {p q : ℕ} (l : Fin p → ℕ → ℝ) (d : ℕ → ℝ)
    (u : Fin q → ℕ → ℝ) (hl : ∀ i j,0 < l i j) (hd : ∀ j,0 < d j)
    (hu : ∀ i j,0 < u i j) (x : FullBand p q) (i j : ℕ) :
    rawFullEntry l d u i j * fullEntry (relativeLDUProduct l d u hl hd hu x) i j =
      rawFullEntry (fun r n => l r n*(1+x.1 r n)) (fun n => d n*(1+x.2.1 n))
        (fun r n => u r n*(1+x.2.2 r n)) i j-rawFullEntry l d u i j := by
  by_cases he : i=j
  · subst j
    have heq (l' : Fin p → ℕ → ℝ) (d' : ℕ → ℝ) (u' : Fin q → ℕ → ℝ) :
        rawFullEntry l' d' u' i i=rawLDUSum l' d' u' 0 0 (q+1) i := by
      simpa using rawFullEntry_lower l' d' u' 0 i
    rw [heq,heq]
    rw [fullEntry_diag]
    change rawLDUSum l d u 0 0 (q+1) i * relativeLDUCoefficient l d u hl hd hu 0 0 (q+1) x i=_
    rw [relativeLDUCoefficient_actual l d u hl hd hu _ _ _ (by omega) (by omega) (by omega)]
    field_simp [ne_of_gt (rawLDUSum_pos l d u hl hd hu 0 0 (q+1) i (by omega) (by omega) (by omega))]
  · by_cases hj : j < i
    · have hm : j+(i-j)=i := by omega
      rw [←hm,rawFullEntry_lower,rawFullEntry_lower]
      by_cases hb : i ≤ j+p
      · have hentry : fullEntry (relativeLDUProduct l d u hl hd hu x) (j+(i-j)) j =
            relativeLDUCoefficient l d u hl hd hu (i-j) 0 (q+1) x j := by
          simp [fullEntry,hm,he,hj,bandEntry,hb,relativeLDUProduct,show i-j-1+1=i-j by omega]
        rw [hentry,relativeLDUCoefficient_actual l d u hl hd hu _ _ _ (by omega) (by omega) (by omega)]
        field_simp [ne_of_gt (rawLDUSum_pos l d u hl hd hu (i-j) 0 (q+1) j (by omega) (by omega) (by omega))]
      · have hout (l' : Fin p → ℕ → ℝ) (d' : ℕ → ℝ) (u' : Fin q → ℕ → ℝ) :
            rawLDUSum l' d' u' (i-j) 0 (q+1) j=0 := by
          apply Finset.sum_eq_zero
          intro t _
          simp [rawLDUTerm,rawTriangular_outside l' (i-j+t) (j-t) (by omega)]
        rw [hout,hout]
        simp
    · have hi : i < j := by omega
      have hm : i+(j-i)=j := by omega
      rw [←hm,rawFullEntry_upper,rawFullEntry_upper]
      by_cases hb : j ≤ i+q
      · have hentry : fullEntry (relativeLDUProduct l d u hl hd hu x) i (i+(j-i)) =
            relativeLDUCoefficient l d u hl hd hu 0 (j-i) (p+1) x i := by
          simp [fullEntry,hm,he,hj,hi,bandEntry,hb,relativeLDUProduct,show j-i-1+1=j-i by omega]
        rw [hentry,relativeLDUCoefficient_actual l d u hl hd hu _ _ _ (by omega) (by omega) (by omega)]
        field_simp [ne_of_gt (rawLDUSum_pos l d u hl hd hu 0 (j-i) (p+1) i (by omega) (by omega) (by omega))]
      · have hout (l' : Fin p → ℕ → ℝ) (d' : ℕ → ℝ) (u' : Fin q → ℕ → ℝ) :
            rawLDUSum l' d' u' 0 (j-i) (p+1) i=0 := by
          apply Finset.sum_eq_zero
          intro t _
          simp [rawLDUTerm,rawTriangular_outside u' (j-i+t) (i-t) (by omega)]
        rw [hout,hout]
        simp

theorem relativeLDUProductDerivative_entry_fin {p q N : ℕ}
    (l : Fin p → ℕ → ℝ) (d : ℕ → ℝ) (u : Fin q → ℕ → ℝ)
    (hl : ∀ i j,0<l i j) (hd : ∀ j,0<d j) (hu : ∀ i j,0<u i j)
    (h : FullBand p q) (i j : Fin N) :
    rawFullEntry l d u i.val j.val *
      fullEntry (relativeLDUProductDerivative l d u hl hd hu 0 h) i.val j.val =
      ∑ k : Fin N,
        ((rawUnitEntry l i.val k.val*bandEntry h.1 i.val k.val)*d k.val*rawUnitEntry u j.val k.val +
         rawUnitEntry l i.val k.val*(d k.val*h.2.1 k.val)*rawUnitEntry u j.val k.val +
         rawUnitEntry l i.val k.val*d k.val*(rawUnitEntry u j.val k.val*bandEntry h.2.2 j.val k.val)) := by
  let f : ℝ → ℝ := fun t => rawFullEntry l d u i.val j.val *
    fullEntry (relativeLDUProduct l d u hl hd hu (t • h)) i.val j.val
  have hline : HasDerivAt (fun t : ℝ => t • h) h 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const h
  have hleft : HasDerivAt f (rawFullEntry l d u i.val j.val *
      fullEntry (relativeLDUProductDerivative l d u hl hd hu 0 h) i.val j.val) 0 := by
    have hf := (fullEntryCLM p q i.val j.val).hasFDerivAt.comp 0
      (relativeLDUProduct_hasFDerivAt l d u hl hd hu 0)
    have hh := hf.comp_hasDerivAt_of_eq 0 hline (by simp)
    convert hh.const_mul (rawFullEntry l d u i.val j.val) using 1 <;> rfl
  have hf : f = fun t =>
      (∑ k : Fin N,
        (rawUnitEntry l i.val k.val+t*(rawUnitEntry l i.val k.val*bandEntry h.1 i.val k.val)) *
        (d k.val+t*(d k.val*h.2.1 k.val)) *
        (rawUnitEntry u j.val k.val+t*(rawUnitEntry u j.val k.val*bandEntry h.2.2 j.val k.val))) -
        rawFullEntry l d u i.val j.val := by
    funext t
    dsimp only [f]
    rw [relativeLDUProduct_actual_entry,rawFullEntry_fin]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    change rawUnitEntry (fun r n => l r n*(1+t*h.1 r n)) i.val k.val *
      (d k.val*(1+t*h.2.1 k.val))*
      rawUnitEntry (fun r n => u r n*(1+t*h.2.2 r n)) j.val k.val = _
    rw [rawUnitEntry_perturbed,rawUnitEntry_perturbed]
    ring
  have hright : HasDerivAt f
      (∑ k : Fin N,
        ((rawUnitEntry l i.val k.val*bandEntry h.1 i.val k.val)*d k.val*rawUnitEntry u j.val k.val +
         rawUnitEntry l i.val k.val*(d k.val*h.2.1 k.val)*rawUnitEntry u j.val k.val +
         rawUnitEntry l i.val k.val*d k.val*(rawUnitEntry u j.val k.val*bandEntry h.2.2 j.val k.val))) 0 := by
    rw [hf]
    apply HasDerivAt.sub_const
    apply HasDerivAt.fun_sum
    intro k _
    have hh := ((scalarAffine_hasDerivAt (rawUnitEntry l i.val k.val)
      (rawUnitEntry l i.val k.val*bandEntry h.1 i.val k.val)).mul
      (scalarAffine_hasDerivAt (d k.val) (d k.val*h.2.1 k.val))).mul
      (scalarAffine_hasDerivAt (rawUnitEntry u j.val k.val)
        (rawUnitEntry u j.val k.val*bandEntry h.2.2 j.val k.val))
    convert hh using 1 <;> first | rfl | (dsimp; ring)
  exact hleft.unique hright

theorem relativeLDUProductDerivative_section {p q : ℕ}
    (l : Fin p → ℕ → ℝ) (d : ℕ → ℝ) (u : Fin q → ℕ → ℝ)
    (hl : ∀ i j,0<l i j) (hd : ∀ j,0<d j) (hu : ∀ i j,0<u i j)
    (h : FullBand p q) (N : ℕ) :
    (fun i j : Fin N => rawFullEntry l d u i.val j.val *
      fullEntry (relativeLDUProductDerivative l d u hl hd hu 0 h) i.val j.val) =
      BandLDU.variation
        (fun i j : Fin N => rawUnitEntry l i.val j.val)
        (Matrix.diagonal (fun i : Fin N => d i.val))
        (fun i j : Fin N => rawUnitEntry u j.val i.val)
        (fun i j : Fin N => rawUnitEntry l i.val j.val*bandEntry h.1 i.val j.val)
        (Matrix.diagonal (fun i : Fin N => d i.val*h.2.1 i.val))
        (fun i j : Fin N => rawUnitEntry u j.val i.val*bandEntry h.2.2 j.val i.val) := by
  ext i j
  rw [relativeLDUProductDerivative_entry_fin l d u hl hd hu h i j]
  simp only [BandLDU.variation,Matrix.add_apply]
  change _ =
    (∑ k : Fin N,(∑ s : Fin N,
      (rawUnitEntry l i.val s.val*bandEntry h.1 i.val s.val)*
        (Matrix.diagonal (fun z : Fin N=>d z.val)) s k)*rawUnitEntry u j.val k.val) +
    (∑ k : Fin N,(∑ s : Fin N,rawUnitEntry l i.val s.val*
        (Matrix.diagonal (fun z : Fin N=>d z.val*h.2.1 z.val)) s k)*rawUnitEntry u j.val k.val) +
    (∑ k : Fin N,(∑ s : Fin N,rawUnitEntry l i.val s.val*
        (Matrix.diagonal (fun z : Fin N=>d z.val)) s k)*
        (rawUnitEntry u j.val k.val*bandEntry h.2.2 j.val k.val))
  simp [Matrix.diagonal,Finset.sum_add_distrib]

#print axioms relativeLDUProduct_actual_entry
#print axioms relativeLDUProductDerivative_section
end BTP.RelativeStability
