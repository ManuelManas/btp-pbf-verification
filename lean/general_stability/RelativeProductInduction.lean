import RelativeExtractionMap
import RelativePositiveFactors
import AnalyticProductDerivative
import AnalyticInduction
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp

noncomputable section
set_option maxHeartbeats 1000000
namespace BTP.RelativeStability
open BTP.GeneralStability

theorem rawCoefficient_outside (c : ℕ → ℕ → ℝ) (k d j : ℕ) (h : k < d) :
    rawCoefficient c k d j=0 := by
  induction k generalizing d j with
  | zero => cases d <;> simp_all [rawCoefficient]
  | succ k ih =>
    cases d with
    | zero => omega
    | succ d => simp only [rawCoefficient,ih (d+1) j (by omega),ih d (j+1) (by omega),zero_mul,add_zero]

theorem rawCoefficient_head (c : ℕ → ℕ → ℝ) (m d j : ℕ) :
    rawCoefficient c (m+1) (d+1) j =
      rawCoefficient (fun i=>c (i+1)) m (d+1) j +
      c 0 (j+d+1)*rawCoefficient (fun i=>c (i+1)) m d j := by
  simp only [rawCoefficient_matrix,productCoefficients_head]
  rw [show j+(d+1)-1=j+d by omega]
  rfl

theorem extendRaw_tail {m : ℕ} (a : Fin (m+1) → ℕ → ℝ) :
    (fun i=>extendRaw a (i+1))=extendRaw (Fin.tail a) := by
  funext i n
  unfold extendRaw
  split_ifs with h₁ h₂ h₂
  · rfl
  · omega
  · omega
  · rfl

theorem factorVariation_tail {m : ℕ} (x : FactorVariations (m+1)) (i : ℕ) :
    factorVariation (m+1) (i+1) x = factorVariation m i (Fin.tail x) := by
  unfold factorVariation
  split_ifs with h₁ h₂ h₂
  · simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply]
    rw [show m+1-(i+1)=m-i by omega]
    rfl
  · omega
  · omega
  · rfl

theorem perturbedRaw_tail {m : ℕ} (a : Fin (m+1) → ℕ → ℝ)
    (x : FactorVariations (m+1)) :
    (fun i n=>extendRaw a (i+1) n*(1+factorVariation (m+1) (i+1) x n))=
    (fun i n=>extendRaw (Fin.tail a) i n*(1+factorVariation m i (Fin.tail x) n)) := by
  funext i n
  rw [factorVariation_tail]
  exact congrArg (fun z=>z i n*(1+factorVariation m i (Fin.tail x) n)) (extendRaw_tail a)

/-- All subdiagonals, including zero and those beyond the bandwidth,
have the same exact multiplicative normalization formula. -/
theorem relativeProduct_actual_all {p : ℕ} (a : Fin p → ℕ → ℝ)
    (ha : ∀ i n,0<a i n) (x : FactorVariations p) (d j : ℕ) :
    rawCoefficient (fun i n=>extendRaw a i n*(1+factorVariation p i x n)) p d j =
      rawCoefficient (extendRaw a) p d j *
      (1+strictCoefficientMap p d (relativeProduct a ha x) j) := by
  cases d with
  | zero => cases p <;> simp [rawCoefficient]
  | succ d =>
    by_cases hd : d < p
    · have h := relative_solution_actual_entry a ha x (relativeProduct a ha x) rfl ⟨d,hd⟩ j
      have hs : strictCoefficientMap p (d+1) (relativeProduct a ha x) = relativeProduct a ha x ⟨d,hd⟩ := by
        unfold strictCoefficientMap
        rw [dite_eq_left (show 0<d+1 ∧ d+1≤p by omega)]
        rfl
      rw [hs]
      exact h
    · rw [rawCoefficient_outside _ _ _ _ (by omega),rawCoefficient_outside _ _ _ _ (by omega),zero_mul]

def relativeEntryCLM (p d j : ℕ) : LowerBand p →L[ℝ] ℝ :=
  (BoundedContinuousFunction.evalCLM ℝ j).comp (strictCoefficientMap p d)

theorem relative_raw_hasDerivAt {p : ℕ} (a : Fin p → ℕ → ℝ)
    (ha : ∀ i n,0<a i n) (h : FactorVariations p) (d j : ℕ) :
    HasDerivAt (fun t : ℝ=>
      rawCoefficient (fun i n=>extendRaw a i n*(1+factorVariation p i (t•h) n)) p d j)
      (rawCoefficient (extendRaw a) p d j *
        strictCoefficientMap p d (relativeProductDerivative a ha 0 h) j) 0 := by
  have hline : HasDerivAt (fun t : ℝ=>t•h) h 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).smul_const h
  have hd := (relativeEntryCLM p d j).hasFDerivAt.comp (0 : FactorVariations p)
    (relativeProduct_hasFDerivAt a ha 0)
  have hh := hd.comp_hasDerivAt_of_eq 0 hline (by simp)
  have hh' := (hh.const_add 1).const_mul (rawCoefficient (extendRaw a) p d j)
  convert hh' using 1 <;> try rfl
  funext t
  exact relativeProduct_actual_all a ha (t•h) d j

theorem relative_head_hasDerivAt {m : ℕ} (a : Fin (m+1) → ℕ → ℝ)
    (h : FactorVariations (m+1)) (n : ℕ) :
    HasDerivAt (fun t : ℝ=>extendRaw a 0 n*(1+factorVariation (m+1) 0 (t•h) n))
      (extendRaw a 0 n*zeroExtension (m+1) (h 0) n) 0 := by
  have he : (fun t : ℝ=>extendRaw a 0 n*(1+factorVariation (m+1) 0 (t•h) n))=
      (fun t : ℝ=>extendRaw a 0 n*(1+t*zeroExtension (m+1) (h 0) n)) := by
    funext t
    simp only [factorVariation, Nat.zero_lt_succ,↓reduceDIte,Nat.sub_zero,
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply,map_smul,
      BoundedContinuousFunction.smul_apply,smul_eq_mul]
    congr 5
  rw [he]
  convert (((hasDerivAt_id (0:ℝ)).mul_const (zeroExtension (m+1) (h 0) n)).const_add 1).const_mul
    (extendRaw a 0 n) using 1 <;> first | rfl | simp only [one_mul]

theorem rawCoefficient_perturbed_zero {p : ℕ} (a : Fin p → ℕ → ℝ) (k d j : ℕ) :
    rawCoefficient (fun i n=>extendRaw a i n*(1+factorVariation p i 0 n)) k d j =
      rawCoefficient (extendRaw a) k d j := by
  congr 1
  funext i n
  simp

theorem relativeProductDerivative_left_entry {m : ℕ} (a : Fin (m+1) → ℕ → ℝ)
    (ha : ∀ i n,0<a i n) (h : FactorVariations (m+1)) (r : Fin (m+1)) (j : ℕ) :
    rawCoefficient (extendRaw a) (m+1) (r.val+1) j *
      relativeProductDerivative a ha 0 h r j =
      rawCoefficient (extendRaw (Fin.tail a)) m (r.val+1) j *
        strictCoefficientMap m (r.val+1)
          (relativeProductDerivative (Fin.tail a) (fun i n=>ha i.succ n) 0 (Fin.tail h)) j +
      (extendRaw a 0 (j+r.val+1)*zeroExtension (m+1) (h 0) (j+r.val+1))*
        rawCoefficient (extendRaw (Fin.tail a)) m r.val j +
      extendRaw a 0 (j+r.val+1)*
        (rawCoefficient (extendRaw (Fin.tail a)) m r.val j *
          strictCoefficientMap m r.val
            (relativeProductDerivative (Fin.tail a) (fun i n=>ha i.succ n) 0 (Fin.tail h)) j) := by
  have hleft := relative_raw_hasDerivAt a ha h (r.val+1) j
  have htail₁ := relative_raw_hasDerivAt (Fin.tail a) (fun i n=>ha i.succ n) (Fin.tail h) (r.val+1) j
  have htail₀ := relative_raw_hasDerivAt (Fin.tail a) (fun i n=>ha i.succ n) (Fin.tail h) r.val j
  have hhead := relative_head_hasDerivAt a h (j+r.val+1)
  have hright := htail₁.add (hhead.mul htail₀)
  have hfun : (fun t : ℝ=>rawCoefficient (fun i n=>extendRaw a i n*(1+factorVariation (m+1) i (t•h) n))
      (m+1) (r.val+1) j)=
      (fun t : ℝ=>
        rawCoefficient (fun i n=>extendRaw (Fin.tail a) i n*(1+factorVariation m i (t•Fin.tail h) n)) m (r.val+1) j +
        (extendRaw a 0 (j+r.val+1)*(1+factorVariation (m+1) 0 (t•h) (j+r.val+1)))*
        rawCoefficient (fun i n=>extendRaw (Fin.tail a) i n*(1+factorVariation m i (t•Fin.tail h) n)) m r.val j) := by
    funext t
    rw [rawCoefficient_head,perturbedRaw_tail]
    rfl
  rw [hfun] at hleft
  have he := hleft.unique hright
  simp only [zero_smul,map_zero,
    BoundedContinuousFunction.coe_zero,Pi.zero_apply,add_zero,mul_one] at he
  have hs : strictCoefficientMap (m+1) (r.val+1) (relativeProductDerivative a ha 0 h)=
      relativeProductDerivative a ha 0 h r := by
    unfold strictCoefficientMap
    rw [dite_eq_left (show 0<r.val+1 ∧ r.val+1≤m+1 by omega)]
    rfl
  rw [hs] at he
  simpa only [add_assoc] using he

/-- Differentiating the genuine arbitrary-growth product commutes with
left extraction. This is the induction step for the relative criterion. -/
theorem relativeProductDerivative_succ {m : ℕ} (a : Fin (m+1) → ℕ → ℝ)
    (ha : ∀ i n,0<a i n) :
    relativeProductDerivative a ha 0 =
      (relativeExtractionDerivative (extendRaw a) (extendRaw_pos a ha) m).comp
        ((ContinuousLinearMap.proj 0).prod
          ((relativeProductDerivative (Fin.tail a) (fun i n=>ha i.succ n) 0).comp (tailCLM m))) := by
  apply ContinuousLinearMap.ext
  intro h
  funext r
  apply BoundedContinuousFunction.ext
  intro j
  have he := relativeProductDerivative_left_entry a ha h r j
  have hz := ne_of_gt (rawCoefficient_pos (extendRaw a) (extendRaw_pos a ha)
    (m+1) (r.val+1) j (by omega))
  change relativeProductDerivative a ha 0 h r j =
    (extendRaw a 0 (j+r.val+1)*productCoefficients (fun i=>extendRaw a (i+1)) m r.val (j+r.val) /
      productCoefficients (extendRaw a) (m+1) (r.val+1) (j+r.val+1))*
        zeroExtension (m+1) (h 0) (j+r.val+1) +
    (productCoefficients (fun i=>extendRaw a (i+1)) m (r.val+1) (j+r.val+1) /
      productCoefficients (extendRaw a) (m+1) (r.val+1) (j+r.val+1))*
        strictCoefficientMap m (r.val+1)
          (relativeProductDerivative (Fin.tail a) (fun i n=>ha i.succ n) 0 (Fin.tail h)) j +
    (extendRaw a 0 (j+r.val+1)*productCoefficients (fun i=>extendRaw a (i+1)) m r.val (j+r.val) /
      productCoefficients (extendRaw a) (m+1) (r.val+1) (j+r.val+1))*
        strictCoefficientMap m r.val
          (relativeProductDerivative (Fin.tail a) (fun i n=>ha i.succ n) 0 (Fin.tail h)) j
  rw [extendRaw_tail]
  simp only [rawCoefficient_matrix,show j+(r.val+1)=j+r.val+1 by omega] at he hz
  field_simp
  nlinarith

#print axioms relativeProductDerivative_succ

theorem relativeProductDerivative_zero_bijective (a : Fin 0 → ℕ → ℝ)
    (ha : ∀ i n,0<a i n) : Function.Bijective (relativeProductDerivative a ha 0) := by
  constructor
  · intro x y _
    exact Subsingleton.elim _ _
  · intro x
    exact ⟨0,Subsingleton.elim _ _⟩

theorem relativeProductDerivative_succ_bijective_iff {m : ℕ} (a : Fin (m+1) → ℕ → ℝ)
    (ha : ∀ i n,0<a i n)
    (hE : Function.Injective (relativeExtractionDerivative (extendRaw a) (extendRaw_pos a ha) m)) :
    Function.Bijective (relativeProductDerivative a ha 0) ↔
      Function.Bijective (relativeExtractionDerivative (extendRaw a) (extendRaw_pos a ha) m) ∧
      Function.Bijective (relativeProductDerivative (Fin.tail a) (fun i n=>ha i.succ n) 0) := by
  rw [relativeProductDerivative_succ]
  have hh := bijective_comp_iff_of_injective
    (relativeExtractionDerivative (extendRaw a) (extendRaw_pos a ha) m)
    (fun h : FactorVariations (m+1)=>(h 0,
      relativeProductDerivative (Fin.tail a) (fun i n=>ha i.succ n) 0 (Fin.tail h))) hE
  rw [headTailDerivative_bijective_iff] at hh
  exact hh

theorem relativeProductDerivative_succ_injective {m : ℕ} (a : Fin (m+1) → ℕ → ℝ)
    (ha : ∀ i n,0<a i n)
    (hE : Function.Injective (relativeExtractionDerivative (extendRaw a) (extendRaw_pos a ha) m))
    (hT : Function.Injective (relativeProductDerivative (Fin.tail a) (fun i n=>ha i.succ n) 0)) :
    Function.Injective (relativeProductDerivative a ha 0) := by
  intro h k he
  rw [relativeProductDerivative_succ] at he
  have hp := hE he
  have h0 : h 0=k 0 := congrArg Prod.fst hp
  have ht : Fin.tail h=Fin.tail k := hT (congrArg Prod.snd hp)
  funext i
  exact Fin.cases h0 (fun j=>congrFun ht j) i

/-- The relative theory uses ratios in the same physical row. It permits
arbitrary positive, unequal growth of the factor entries. -/
def RelativeAdjacentGeometric {p : ℕ} (a : Fin p → ℕ → ℝ) : Prop :=
  ∀ (i : ℕ) (hi : i+1<p),
    GeometricDecay (fun n=>a ⟨i,by omega⟩ n/a ⟨i+1,hi⟩ n)

theorem relativeAdjacentGeometric_succ_iff {m : ℕ} (a : Fin (m+1) → ℕ → ℝ) :
    RelativeAdjacentGeometric a ↔
      (∀ hm : 0<m,GeometricDecay (fun n=>a 0 n/a ⟨1,by omega⟩ n)) ∧
      RelativeAdjacentGeometric (Fin.tail a) := by
  constructor
  · intro h
    refine ⟨?_,?_⟩
    · intro hm
      simpa only [Fin.mk_zero] using h 0 (by omega)
    · intro i hi
      exact h (i+1) (by omega)
  · rintro ⟨hh,ht⟩ i hi
    cases i with
    | zero => simpa only [Fin.mk_zero] using hh (by omega)
    | succ i => exact ht i (by omega)

#print axioms relativeProductDerivative_succ_bijective_iff
#print axioms relativeAdjacentGeometric_succ_iff

end BTP.RelativeStability
