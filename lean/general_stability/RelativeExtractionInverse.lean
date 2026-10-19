import RelativeExtractionMap

noncomputable section
namespace BTP.RelativeStability
open BTP.Stability BTP.GeneralStability
set_option maxHeartbeats 2000000

theorem eliminate_smul (a : ℕ → ℝ) (E : RowCoefficients) (t : ℝ) (s n : ℕ) :
    eliminate a (fun s n=>t*E s n) s n=t*eliminate a E s n := by
  induction s generalizing n with
  | zero => simp [eliminate]
  | succ s ih => simp only [eliminate, ih]; ring

theorem relativeBandVariation_add (c : ℕ → ℕ → ℝ) (m : ℕ)
    (E F : LowerBand m) (s n : ℕ) :
    relativeBandVariation c m (E+F) s n =
      relativeBandVariation c m E s n + relativeBandVariation c m F s n := by
  unfold relativeBandVariation
  split_ifs <;> simp [mul_add]

theorem relativeBandVariation_smul (c : ℕ → ℕ → ℝ) (m : ℕ)
    (E : LowerBand m) (t : ℝ) (s n : ℕ) :
    relativeBandVariation c m (t • E) s n = t*relativeBandVariation c m E s n := by
  unfold relativeBandVariation
  split_ifs <;> simp [mul_left_comm]

def normalizedForcing (c : ℕ → ℕ → ℝ) (m : ℕ) (E : LowerBand (m+1)) (n : ℕ) : ℝ :=
  eliminate (c 0) (relativeBandVariation c (m+1) E) (m+1) (n+m+1) /
    scale c m (n+m+1)

theorem normalizedForcing_bound (c : ℕ → ℕ → ℝ) (hc : ∀ i n,0<c i n)
    (m : ℕ) (K : ℝ) (hK : 1≤K)
    (hcomp : ∀ i j n, i≤j → c i n≤K*c j n) (E : LowerBand (m+1)) (n : ℕ) :
    |normalizedForcing c m E n|≤extractionBound (m+1) K*‖E‖ := by
  have hb := relative_forcing_bound c (fun i n=>(hc i n).le) K hK hcomp (m+1)
    (relativeBandVariation c (m+1) E) ‖E‖ (norm_nonneg _) (fun s n _=>relativeBandVariation_bound c
      (fun i n=>(hc i n).le) (m+1) E s n) (m+1) (n+m+1) (le_refl _)
  rw [lastPath_all_eq_scale] at hb
  unfold normalizedForcing
  rw [abs_div, abs_of_pos (scale_pos c hc _ _)]
  apply (div_le_iff₀ (scale_pos c hc _ _)).mpr
  calc
    _ ≤ _ := hb
    _ = _ := by unfold extractionBound; ring

def relativeForcingMap (c : ℕ → ℕ → ℝ) (hc : ∀ i n,0<c i n)
    (m : ℕ) (K : ℝ) (hK : 1≤K)
    (hcomp : ∀ i j n, i≤j → c i n≤K*c j n) : LowerBand (m+1) →L[ℝ] Seq :=
  let F : LowerBand (m+1) →ₗ[ℝ] Seq :=
    { toFun := fun E=>ofAbsBound (normalizedForcing c m E) (extractionBound (m+1) K*‖E‖)
        (normalizedForcing_bound c hc m K hK hcomp E)
      map_add' := by
        intro E F
        apply BoundedContinuousFunction.ext
        intro n
        change normalizedForcing c m (E+F) n = normalizedForcing c m E n+normalizedForcing c m F n
        unfold normalizedForcing
        have he : relativeBandVariation c (m+1) (E+F)=fun s n=>relativeBandVariation c (m+1) E s n+
            relativeBandVariation c (m+1) F s n := by funext s n; exact relativeBandVariation_add c _ E F s n
        rw [he, eliminate_add, add_div]
      map_smul' := by
        intro t E
        apply BoundedContinuousFunction.ext
        intro n
        change normalizedForcing c m (t • E) n=t*normalizedForcing c m E n
        unfold normalizedForcing
        have he : relativeBandVariation c (m+1) (t • E)=fun s n=>t*relativeBandVariation c (m+1) E s n := by
          funext s n; exact relativeBandVariation_smul c _ E t s n
        rw [he, eliminate_smul]
        ring }
  F.mkContinuous (extractionBound (m+1) K) (by
    intro E
    apply BoundedContinuousFunction.norm_le_of_nonempty.mpr
    exact normalizedForcing_bound c hc m K hK hcomp E)

@[simp] theorem relativeForcingMap_apply (c : ℕ → ℕ → ℝ) (hc : ∀ i n,0<c i n)
    (m : ℕ) (K : ℝ) (hK : 1≤K)
    (hcomp : ∀ i j n, i≤j → c i n≤K*c j n) (E : LowerBand (m+1)) (n : ℕ) :
    relativeForcingMap c hc m K hK hcomp E n=normalizedForcing c m E n := rfl

def relativeRemainderRaw (c : ℕ → ℕ → ℝ) (m : ℕ) (x : Seq)
    (E : LowerBand (m+1)) : RowCoefficients :=
  remainderCoefficients (c 0) (relativeHeadVariation c (m+1) x)
    (productCoefficients (fun i=>c (i+1)) m) (relativeBandVariation c (m+1) E)

def normalizedRemainder (c : ℕ → ℕ → ℝ) (m : ℕ) (x : Seq)
    (E : LowerBand (m+1)) (r : Fin m) (j : ℕ) : ℝ :=
  relativeRemainderRaw c m x E (r.val+1) (j+r.val+1) /
    productCoefficients (fun i=>c (i+1)) m (r.val+1) (j+r.val+1)

theorem relativeHeadVariation_bound (c : ℕ → ℕ → ℝ) (hc : ∀ i n,0≤c i n)
    (m : ℕ) (x : Seq) (n : ℕ) : |relativeHeadVariation c m x n|≤‖x‖*c 0 n := by
  unfold relativeHeadVariation
  split_ifs with hn
  · rw [abs_mul, abs_of_nonneg (hc 0 n)]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (boundedSequence_abs_le x (n-m)) (hc 0 n)
  · simp only [mul_zero, abs_zero]
    exact mul_nonneg (norm_nonneg _) (hc 0 n)

theorem productCoefficients_pos (c : ℕ → ℕ → ℝ) (hc : ∀ i n,0<c i n)
    (m s n : ℕ) (hs : s≤m) : 0<productCoefficients c m s n :=
  (lastPath_pos c hc m s n).trans_le (lastPath_le_productCoefficients c (fun i n=>(hc i n).le) m s n hs)

theorem normalizedRemainder_bound (c : ℕ → ℕ → ℝ) (hc : ∀ i n,0<c i n)
    (m : ℕ) (K : ℝ) (hK : 1≤K)
    (hcomp : ∀ i j n, i≤j → c i n≤K*c j n)
    (x : Seq) (E : LowerBand (m+1)) (r : Fin m) (j : ℕ) :
    |normalizedRemainder c m x E r j|≤extractionBound (m+1) K*(‖E‖+‖x‖) := by
  have hb := relative_remainder_bound c (fun i n=>(hc i n).le) K hK hcomp (m+1) (by omega)
    (relativeBandVariation c (m+1) E) ‖E‖ (norm_nonneg _)
    (fun s n _=>relativeBandVariation_bound c (fun i n=>(hc i n).le) (m+1) E s n)
    (relativeHeadVariation c (m+1) x) ‖x‖ (norm_nonneg _)
    (relativeHeadVariation_bound c (fun i n=>(hc i n).le) (m+1) x)
    (r.val+1) (j+r.val+1) (by omega)
  have hp := productCoefficients_pos (fun i=>c (i+1)) (fun i n=>hc (i+1) n)
    m (r.val+1) (j+r.val+1) (by omega)
  unfold normalizedRemainder relativeRemainderRaw remainderCoefficients
  rw [eliminate_sub, abs_div, abs_of_pos hp]
  apply (div_le_iff₀ hp).mpr
  simpa only [Nat.add_sub_cancel] using hb

theorem relativeHeadVariation_add (c : ℕ → ℕ → ℝ) (m : ℕ) (x y : Seq) (n : ℕ) :
    relativeHeadVariation c m ((x+y : Seq) : ℕ → ℝ) n=relativeHeadVariation c m x n+relativeHeadVariation c m y n := by
  unfold relativeHeadVariation
  split_ifs <;> simp [mul_add]

theorem relativeHeadVariation_smul (c : ℕ → ℕ → ℝ) (m : ℕ) (x : Seq) (t : ℝ) (n : ℕ) :
    relativeHeadVariation c m ((t • x : Seq) : ℕ → ℝ) n=t*relativeHeadVariation c m x n := by
  unfold relativeHeadVariation
  split_ifs <;> simp [mul_left_comm]

theorem relativeRemainderRaw_add (c : ℕ → ℕ → ℝ) (m : ℕ) (x y : Seq)
    (E F : LowerBand (m+1)) (s n : ℕ) :
    relativeRemainderRaw c m (x+y) (E+F) s n=
      relativeRemainderRaw c m x E s n+relativeRemainderRaw c m y F s n := by
  unfold relativeRemainderRaw remainderCoefficients
  have he : (fun s n=>relativeBandVariation c (m+1) (E+F) s n-
      leftVariation (relativeHeadVariation c (m+1) ((x+y : Seq) : ℕ → ℝ)) (productCoefficients (fun i=>c (i+1)) m) s n) =
      fun s n=>(relativeBandVariation c (m+1) E s n-
        leftVariation (relativeHeadVariation c (m+1) x) (productCoefficients (fun i=>c (i+1)) m) s n)+
        (relativeBandVariation c (m+1) F s n-
        leftVariation (relativeHeadVariation c (m+1) y) (productCoefficients (fun i=>c (i+1)) m) s n) := by
    funext s n
    rw [relativeBandVariation_add]
    cases s <;> simp only [leftVariation, relativeHeadVariation_add] <;> ring
  rw [he, eliminate_add]

theorem relativeRemainderRaw_smul (c : ℕ → ℕ → ℝ) (m : ℕ) (x : Seq)
    (E : LowerBand (m+1)) (t : ℝ) (s n : ℕ) :
    relativeRemainderRaw c m (t • x) (t • E) s n=t*relativeRemainderRaw c m x E s n := by
  unfold relativeRemainderRaw remainderCoefficients
  have he : (fun s n=>relativeBandVariation c (m+1) (t • E) s n-
      leftVariation (relativeHeadVariation c (m+1) ((t • x : Seq) : ℕ → ℝ)) (productCoefficients (fun i=>c (i+1)) m) s n) =
      fun s n=>t*(relativeBandVariation c (m+1) E s n-
        leftVariation (relativeHeadVariation c (m+1) x) (productCoefficients (fun i=>c (i+1)) m) s n) := by
    funext s n
    rw [relativeBandVariation_smul]
    cases s <;> simp only [leftVariation, relativeHeadVariation_smul] <;> ring
  rw [he, eliminate_smul]

def relativeRemainderMap (c : ℕ → ℕ → ℝ) (hc : ∀ i n,0<c i n)
    (m : ℕ) (K : ℝ) (hK : 1≤K)
    (hcomp : ∀ i j n, i≤j → c i n≤K*c j n) :
    Seq × LowerBand (m+1) →L[ℝ] LowerBand m :=
  ContinuousLinearMap.pi (fun r=>
    let R : Seq × LowerBand (m+1) →ₗ[ℝ] Seq :=
      { toFun := fun v=>ofAbsBound (normalizedRemainder c m v.1 v.2 r)
          (extractionBound (m+1) K*(‖v.2‖+‖v.1‖))
          (normalizedRemainder_bound c hc m K hK hcomp v.1 v.2 r)
        map_add' := by
          intro v w
          apply BoundedContinuousFunction.ext
          intro n
          change normalizedRemainder c m (v.1+w.1) (v.2+w.2) r n = _
          unfold normalizedRemainder
          rw [relativeRemainderRaw_add, add_div]
          rfl
        map_smul' := by
          intro t v
          apply BoundedContinuousFunction.ext
          intro n
          change normalizedRemainder c m (t • v.1) (t • v.2) r n = _
          unfold normalizedRemainder
          rw [relativeRemainderRaw_smul]
          change t*_ / _=t*(_ / _)
          ring }
    R.mkContinuous (2*extractionBound (m+1) K) (by
      intro v
      apply BoundedContinuousFunction.norm_le_of_nonempty.mpr
      intro n
      change |normalizedRemainder c m v.1 v.2 r n|≤_
      calc
        _ ≤ extractionBound (m+1) K*(‖v.2‖+‖v.1‖) := normalizedRemainder_bound c hc m K hK hcomp v.1 v.2 r n
        _ ≤ extractionBound (m+1) K*(‖v‖+‖v‖) :=
          mul_le_mul_of_nonneg_left (add_le_add (norm_snd_le v) (norm_fst_le v)) (by unfold extractionBound; positivity)
        _ = _ := by ring))

@[simp] theorem relativeRemainderMap_apply (c : ℕ → ℕ → ℝ) (hc : ∀ i n,0<c i n)
    (m : ℕ) (K : ℝ) (hK : 1≤K)
    (hcomp : ∀ i j n, i≤j → c i n≤K*c j n)
    (x : Seq) (E : LowerBand (m+1)) (r : Fin m) (j : ℕ) :
    relativeRemainderMap c hc m K hK hcomp (x,E) r j=normalizedRemainder c m x E r j := rfl

theorem realized_relativeRemainder (c : ℕ → ℕ → ℝ) (hc : ∀ i n,0<c i n)
    (m : ℕ) (K : ℝ) (hK : 1≤K)
    (hcomp : ∀ i j n, i≤j → c i n≤K*c j n)
    (x : Seq) (E : LowerBand (m+1)) (s n : ℕ) (hs : s≤m) (hn : s≤n) :
    relativeBandVariation (fun i=>c (i+1)) m
      (relativeRemainderMap c hc m K hK hcomp (x,E)) s n = relativeRemainderRaw c m x E s n := by
  cases s with
  | zero => simp [relativeRemainderRaw, remainderCoefficients_zero]
  | succ s =>
    let r : Fin m := ⟨s, by omega⟩
    have hrow : n-(s+1)+r.val+1=n := by dsimp [r]; omega
    have hh := relativeBandVariation_coordinate (fun i=>c (i+1)) m
      (relativeRemainderMap c hc m K hK hcomp (x,E)) r (n-(s+1))
    rw [hrow] at hh
    change relativeBandVariation (fun i=>c (i+1)) m
      (relativeRemainderMap c hc m K hK hcomp (x,E)) (r.val+1) n = _
    rw [hh, relativeRemainderMap_apply]
    unfold normalizedRemainder
    rw [hrow]
    exact mul_div_cancel₀ _ (ne_of_gt (productCoefficients_pos (fun i=>c (i+1))
      (fun i n=>hc (i+1) n) m (r.val+1) n hs))

theorem relativeExtraction_remainder_solves (c : ℕ → ℕ → ℝ) (hc : ∀ i n,0<c i n)
    (m : ℕ) (K : ℝ) (hK : 1≤K)
    (hcomp : ∀ i j n, i≤j → c i n≤K*c j n)
    (x : Seq) (E : LowerBand (m+1))
    (htop : ∀ n, m+1≤n → relativeRemainderRaw c m x E (m+1) n=0) :
    relativeExtractionDerivative c hc m (x,relativeRemainderMap c hc m K hK hcomp (x,E)) = E := by
  funext r
  apply BoundedContinuousFunction.ext
  intro j
  rw [relativeExtractionDerivative_actual]
  let R := relativeRemainderMap c hc m K hK hcomp (x,E)
  have hR (s n : ℕ) (hs : s≤m+1) (hn : s≤n) :
      relativeBandVariation (fun i=>c (i+1)) m R s n=relativeRemainderRaw c m x E s n := by
    by_cases hh : s≤m
    · exact realized_relativeRemainder c hc m K hK hcomp x E s n hh hn
    · have he : s=m+1 := by omega
      subst s
      rw [htop n hn]
      simp [relativeBandVariation]
  have hcur := hR (r.val+1) (j+r.val+1) (by omega) (by omega)
  have hprev := hR r.val (j+r.val) (by omega) (by omega)
  change extractionDerivative (c 0) (relativeHeadVariation c (m+1) x)
    (productCoefficients (fun i=>c (i+1)) m)
    (relativeBandVariation (fun i=>c (i+1)) m R) (r.val+1) (j+r.val+1) /
      productCoefficients c (m+1) (r.val+1) (j+r.val+1) = E r j
  have heq : extractionDerivative (c 0) (relativeHeadVariation c (m+1) x)
      (productCoefficients (fun i=>c (i+1)) m)
      (relativeBandVariation (fun i=>c (i+1)) m R) (r.val+1) (j+r.val+1) =
      relativeBandVariation c (m+1) E (r.val+1) (j+r.val+1) := by
    change relativeHeadVariation c (m+1) x (j+r.val+1)*productCoefficients (fun i=>c (i+1)) m r.val (j+r.val+1-1)+
      relativeBandVariation (fun i=>c (i+1)) m R (r.val+1) (j+r.val+1)+
      c 0 (j+r.val+1)*relativeBandVariation (fun i=>c (i+1)) m R r.val (j+r.val+1-1) = _
    rw [show j+r.val+1-1=j+r.val by omega, hcur, hprev]
    exact remainderCoefficients_solves (c 0) (relativeHeadVariation c (m+1) x)
      (productCoefficients (fun i=>c (i+1)) m) (relativeBandVariation c (m+1) E) r.val (j+r.val+1)
  rw [heq, relativeBandVariation_coordinate]
  exact mul_div_cancel_left₀ _ (ne_of_gt (productCoefficients_pos c hc (m+1) (r.val+1) (j+r.val+1) (by omega)))

/-- Bounded right inverse of the genuine relative extraction derivative.
This is the full forcing/remainder estimate, not merely a scalar proxy. -/
theorem relativeExtraction_rightInverse_of_comparable (c : ℕ → ℕ → ℝ)
    (hc : ∀ i n,0<c i n) (m : ℕ) (K : ℝ) (hK : 1≤K)
    (hcomp : ∀ i j n, i≤j → c i n≤K*c j n)
    (hg : ∀ j, j<m → GeometricDecay (fun n=>c j n/c (j+1) n)) :
    ∃ R : LowerBand (m+1) →L[ℝ] Seq × LowerBand m,
      (relativeExtractionDerivative c hc m).comp R=ContinuousLinearMap.id ℝ _ := by
  obtain ⟨S,hS⟩ := normalized_residual_bounded_inverse c hc (m+1) (by omega)
    (fun j hj=>hg j (by omega))
  let H := S.comp (relativeForcingMap c hc m K hK hcomp)
  let R := (relativeRemainderMap c hc m K hK hcomp).comp (H.prod (ContinuousLinearMap.id ℝ _))
  refine ⟨H.prod R, ?_⟩
  apply ContinuousLinearMap.ext
  intro E
  change relativeExtractionDerivative c hc m (H E, relativeRemainderMap c hc m K hK hcomp (H E,E))=E
  apply relativeExtraction_remainder_solves c hc m K hK hcomp
  intro n hn
  have hh := hS (relativeForcingMap c hc m K hK hcomp E) (n-(m+1))
  have hrow : n-(m+1)+(m+1)=n := by omega
  rw [hrow, relativeForcingMap_apply] at hh
  unfold normalizedForcing at hh
  rw [show n-(m+1)+m+1=n by omega] at hh
  change scalarResidual (c 0) (relativeHeadVariation c (m+1) (H E))
      (productCoefficients (fun j=>c (j+1)) m) m n / scale c m n =
    eliminate (c 0) (relativeBandVariation c (m+1) E) (m+1) n / scale c m n at hh
  have he := (div_left_inj' (ne_of_gt (scale_pos c hc m n))).mp hh
  unfold relativeRemainderRaw remainderCoefficients
  rw [eliminate_sub]
  change eliminate (c 0) (relativeBandVariation c (m+1) E) (m+1) n -
    scalarResidual (c 0) (relativeHeadVariation c (m+1) (H E))
      (productCoefficients (fun i=>c (i+1)) m) m n=0
  rw [he, sub_self]

#print axioms relativeExtraction_remainder_solves
#print axioms relativeExtraction_rightInverse_of_comparable
#print axioms normalizedForcing_bound
#print axioms normalizedRemainder_bound
#print axioms relativeRemainderMap_apply
end BTP.RelativeStability
