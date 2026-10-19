import RelativeNormalization

/-! Relative scalar extraction for arbitrarily growing positive factors.
The raw recurrence is identified with actual coefficient elimination before
bounded operators are introduced. No uniform bound is imposed on the factors. -/

noncomputable section
namespace BTP.RelativeStability
open BTP.Stability BTP.GeneralStability

/-- Composition in extraction order, on all real sequences. -/
def rawDifferenceProduct (w : ℕ → ℕ → ℝ) : ℕ → (ℕ → ℝ) → (ℕ → ℝ)
  | 0, f => f
  | k+1, f => differenceFun (w k) (rawDifferenceProduct w k f)

/-- Its formal triangular inverse, using only finitely many entries in each row. -/
def rawSolutionProduct (w : ℕ → ℕ → ℝ) : ℕ → (ℕ → ℝ) → (ℕ → ℝ)
  | 0, f => f
  | k+1, f => rawSolutionProduct w k (forwardSolution (w k) f)

theorem forwardSolution_difference (w f : ℕ → ℝ) :
    forwardSolution w (differenceFun w f) = f := by
  funext n
  induction n with
  | zero => rfl
  | succ n ih => simp only [forwardSolution_succ, differenceFun, ih]; ring

theorem difference_forwardSolution (w f : ℕ → ℝ) :
    differenceFun w (forwardSolution w f) = f := by
  funext n
  cases n with
  | zero => rfl
  | succ n => simp only [differenceFun, forwardSolution_succ]; ring

theorem rawSolution_difference (w : ℕ → ℕ → ℝ) (k : ℕ) (f : ℕ → ℝ) :
    rawSolutionProduct w k (rawDifferenceProduct w k f) = f := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [rawSolutionProduct, rawDifferenceProduct, forwardSolution_difference, ih]

theorem rawDifference_solution (w : ℕ → ℕ → ℝ) (k : ℕ) (f : ℕ → ℝ) :
    rawDifferenceProduct w k (rawSolutionProduct w k f) = f := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih =>
    simp only [rawSolutionProduct, rawDifferenceProduct, ih, difference_forwardSolution]

theorem forwardSolution_nonneg (w f : ℕ → ℝ) (hw : ∀ n, 0≤w n)
    (hf : ∀ n, 0≤f n) (n : ℕ) : 0≤forwardSolution w f n := by
  induction n with
  | zero => exact hf 0
  | succ n ih => exact add_nonneg (hf _) (mul_nonneg (hw _) ih)

theorem forwardSolution_ge_input (w f : ℕ → ℝ) (hw : ∀ n, 0≤w n)
    (hf : ∀ n, 0≤f n) (n : ℕ) : f n≤forwardSolution w f n := by
  cases n with
  | zero => exact le_refl _
  | succ n =>
    exact le_add_of_nonneg_right (mul_nonneg (hw _) (forwardSolution_nonneg w f hw hf n))

theorem forwardSolution_mono (w f g : ℕ → ℝ) (hw : ∀ n, 0≤w n)
    (hfg : ∀ n, f n≤g n) (n : ℕ) : forwardSolution w f n≤forwardSolution w g n := by
  induction n with
  | zero => exact hfg 0
  | succ n ih => exact add_le_add (hfg _) (mul_le_mul_of_nonneg_left ih (hw _))

theorem rawSolutionProduct_mono (w : ℕ → ℕ → ℝ) (hw : ∀ k n, 0≤w k n)
    (k : ℕ) (f g : ℕ → ℝ) (hfg : ∀ n, f n≤g n) (n : ℕ) :
    rawSolutionProduct w k f n≤rawSolutionProduct w k g n := by
  induction k generalizing f g with
  | zero => exact hfg n
  | succ k ih =>
    exact ih _ _ (forwardSolution_mono (w k) f g (hw k) hfg)

/-- Every later positive inverse can only increase the forcing for the
first inverse. This remains true before any boundedness is known. -/
theorem first_rowSum_le_solutionProduct (w : ℕ → ℕ → ℝ)
    (hw : ∀ k n, 0≤w k n) (k n : ℕ) :
    rowSum (w 0) n≤rawSolutionProduct w (k+1) (fun _=>1) n := by
  induction k with
  | zero => simp [rawSolutionProduct, forwardSolution_one]
  | succ k ih =>
    exact ih.trans (rawSolutionProduct_mono w hw (k+1) _ _
      (forwardSolution_ge_input (w (k+1)) (fun _=>1) (hw _) (fun _=>by norm_num)) n)

/-- A bounded solution for the single positive forcing 1 already forces
geometric decay of the first weight, even if all weights began unbounded. -/
theorem geometric_of_bounded_raw_solution (w : ℕ → ℕ → ℝ)
    (hw : ∀ k n, 0≤w k n) (k : ℕ) (v : ℕ → ℝ) (M : ℝ)
    (hv : ∀ n, v n≤M) (he : rawDifferenceProduct w (k+1) v = fun _=>1) :
    GeometricDecay (w 0) := by
  have hsol : rawSolutionProduct w (k+1) (fun _=>1) = v := by
    rw [←he, rawSolution_difference]
  apply geometric_of_rowSum_bound (hw 0)
  intro n
  exact (first_rowSum_le_solutionProduct w hw k n).trans (by simpa [hsol] using hv n)

/-- A relative factor variation is extended by zero through the fixed rows. -/
def relativeHeadVariation (c : ℕ → ℕ → ℝ) (m : ℕ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  c 0 n * if m≤n then x (n-m) else 0

theorem relativeHeadVariation_initial (c : ℕ → ℕ → ℝ) (m : ℕ)
    (x : ℕ → ℝ) (n : ℕ) (hn : n<m) : relativeHeadVariation c m x n=0 := by
  simp [relativeHeadVariation, show ¬m≤n by omega]

theorem firstOrderProduct_initial (a : ℕ → ℝ) (b : ℕ → ℕ → ℝ)
    (h : ℕ → ℝ) (m : ℕ) (hh : ∀ n<m, h n=0) (k n : ℕ) (hn : n<m) :
    firstOrderProduct a b h k n=0 := by
  induction k generalizing n with
  | zero => exact hh n hn
  | succ k ih => simp [firstOrderProduct, ih n hn, ih (n-1) (by omega)]

/-- The exact weights of the normalized extraction equations, with row m
identified with coordinate zero and zero preceding initial data. -/
def extractionWeight (c : ℕ → ℕ → ℝ) (m j n : ℕ) : ℝ := theta c j (n+m)

theorem extractionWeight_nonneg (c : ℕ → ℕ → ℝ) (hc : ∀ i n, 0<c i n)
    (m j n : ℕ) : 0≤extractionWeight c m j n := by
  unfold extractionWeight theta
  exact Finset.prod_nonneg (fun _ _ => div_nonneg (hc _ _).le (hc _ _).le)

theorem relative_firstOrderProduct (c : ℕ → ℕ → ℝ) (hc : ∀ i n, 0<c i n)
    (m : ℕ) (hm : 0<m) (x : ℕ → ℝ) (k n : ℕ) :
    firstOrderProduct (c 0) (fun j=>c (j+1)) (relativeHeadVariation c m x) k (n+m) =
      scale c k (n+m) * rawDifferenceProduct (extractionWeight c m) k x n := by
  induction k generalizing n with
  | zero => simp [firstOrderProduct, relativeHeadVariation, scale, rawDifferenceProduct]
  | succ k ih =>
    cases n with
    | zero =>
      have hz := firstOrderProduct_initial (c 0) (fun j=>c (j+1))
        (relativeHeadVariation c m x) m (relativeHeadVariation_initial c m x) k (m-1) (by omega)
      simp only [Nat.zero_add, firstOrderProduct, hz, mul_zero, sub_zero,
        rawDifferenceProduct, differenceFun, scale_succ]
      have hi := ih 0
      simp only [Nat.zero_add] at hi
      rw [show m-(k+1)=m-k-1 by omega, hi]
      ring
    | succ n =>
      have hn : n+1+m-1=n+m := by omega
      simp only [firstOrderProduct, hn, rawDifferenceProduct, differenceFun]
      rw [ih (n+1), ih n]
      have hs := scale_succ c k (n+1+m)
      have hr := scale_ratio c hc k (n+1+m)
      have hne := ne_of_gt (scale_pos c hc (k+1) (n+1+m))
      have ht : scale c (k+1) (n+1+m) * extractionWeight c m k (n+1) =
          c 0 (n+1+m)*scale c k (n+m) := by
        unfold extractionWeight
        rw [←hr, hn]
        field_simp
      have hind : n+1+m-(k+1)=n+1+m-k-1 := by omega
      rw [hind]
      calc
        _ = scale c (k+1) (n+1+m)*rawDifferenceProduct (extractionWeight c m) k x (n+1) -
          (scale c (k+1) (n+1+m)*extractionWeight c m k (n+1))*
            rawDifferenceProduct (extractionWeight c m) k x n := by rw [ht, hs]; ring
        _ = _ := by ring

/-- Actual elimination residual divided by the positive deepest entry.
This bridge uses the proved bidiagonal coefficient identity. -/
theorem normalized_residual_eq (c : ℕ → ℕ → ℝ) (hc : ∀ i n, 0<c i n)
    (m : ℕ) (hm : 0<m) (x : ℕ → ℝ) (k n : ℕ) :
    scalarResidual (c 0) (relativeHeadVariation c m x)
      (productCoefficients (fun j=>c (j+1)) k) k (n+m) / scale c k (n+m) =
      rawDifferenceProduct (extractionWeight c m) k x n := by
  rw [scalarResidual_eq_firstOrderProduct, relative_firstOrderProduct c hc m hm]
  exact mul_div_cancel_left₀ _ (ne_of_gt (scale_pos c hc _ _))

/-- Uniform geometric bounds produce an actual bounded linear formal
inverse for the entire normalized extraction equation. -/
theorem bounded_rawSolutionProduct (w : ℕ → ℕ → ℝ)
    (hw : ∀ k n, 0≤w k n) (k : ℕ)
    (hg : ∀ j<k, GeometricDecay (w j)) :
    ∃ S : Seq →L[ℝ] Seq, ∀ f n, S f n = rawSolutionProduct w k f n := by
  induction k with
  | zero => exact ⟨ContinuousLinearMap.id ℝ Seq, fun _ _=>rfl⟩
  | succ k ih =>
    obtain ⟨S,hS⟩ := ih (fun j hj=>hg j (by omega))
    obtain ⟨M,hM⟩ := (rowSum_bounded_iff_geometric (hw k)).mpr (hg k (by omega))
    refine ⟨S.comp (solutionMap (hw k) M hM), ?_⟩
    intro f n
    change S (solutionMap (hw k) M hM f) n = _
    rw [hS]
    rfl

theorem extractionWeight_geometric (c : ℕ → ℕ → ℝ) (hc : ∀ i n, 0<c i n)
    (m j : ℕ) (hj : j+2≤m)
    (hg : ∀ l≤j, GeometricDecay (fun n=>c l n/c (l+1) n)) :
    GeometricDecay (extractionWeight c m j) := by
  have hh := theta_geometric c hc j hg
  have hs := (GeometricDecay.shift_iff
    (fun n=>extractionWeight_nonneg c hc (j+2) j n) (m-(j+2))).mpr hh
  have he : (fun n=>extractionWeight c (j+2) j (m-(j+2)+n)) =
      extractionWeight c m j := by
    funext n
    unfold extractionWeight
    congr 1
    omega
  exact he ▸ hs

/-- Sufficiency in the scalar extraction equation, with arbitrary growth
of the original factors and an actual continuous linear inverse. -/
theorem normalized_residual_bounded_inverse (c : ℕ → ℕ → ℝ)
    (hc : ∀ i n, 0<c i n) (m : ℕ) (hm : 0<m)
    (hg : ∀ j, j+1<m → GeometricDecay (fun n=>c j n/c (j+1) n)) :
    ∃ S : Seq →L[ℝ] Seq, ∀ f n,
      scalarResidual (c 0) (relativeHeadVariation c m (S f))
        (productCoefficients (fun j=>c (j+1)) (m-1)) (m-1) (n+m) /
          scale c (m-1) (n+m) = f n := by
  obtain ⟨S,hS⟩ := bounded_rawSolutionProduct (extractionWeight c m)
    (extractionWeight_nonneg c hc m) (m-1) (by
      intro j hj
      exact extractionWeight_geometric c hc m j (by omega)
        (fun l hl=>hg l (by omega)))
  refine ⟨S, ?_⟩
  intro f n
  rw [normalized_residual_eq c hc m hm]
  have he : (S f : ℕ → ℝ)=rawSolutionProduct (extractionWeight c m) (m-1) f := by
    funext j
    exact hS f j
  rw [he, rawDifference_solution]

/-- Necessity for the first adjacent same-row ratio. No boundedness of
intermediate operators or factor entries is used. -/
theorem adjacent_geometric_of_normalized_residual (c : ℕ → ℕ → ℝ)
    (hc : ∀ i n, 0<c i n) (m : ℕ) (hm : 2≤m) (v : Seq)
    (he : ∀ n, scalarResidual (c 0) (relativeHeadVariation c m v)
        (productCoefficients (fun j=>c (j+1)) (m-1)) (m-1) (n+m) /
          scale c (m-1) (n+m) = 1) :
    GeometricDecay (fun n=>c 0 n/c 1 n) := by
  have hdiff : rawDifferenceProduct (extractionWeight c m) (m-1) v = fun _=>1 := by
    funext n
    simpa only [normalized_residual_eq c hc m (by omega)] using he n
  have hgeo := geometric_of_bounded_raw_solution (extractionWeight c m)
    (extractionWeight_nonneg c hc m) (m-2) v ‖v‖
    (fun n=>(le_abs_self _).trans (boundedSequence_abs_le v n)) (by
      simpa only [show m-2+1=m-1 by omega] using hdiff)
  have heq : extractionWeight c m 0 = fun n=>c 0 (m-1+n)/c 1 (m-1+n) := by
    funext n
    simp only [extractionWeight, theta, Nat.zero_add, Finset.prod_range_one,
      Nat.sub_zero]
    rw [show n+m-1=m-1+n by omega]
  rw [heq] at hgeo
  exact BTP.FreeScalar.geometric_of_shift
    (fun n=>div_nonneg (hc 0 n).le (hc 1 n).le) (m-1) hgeo

#print axioms bounded_rawSolutionProduct
#print axioms normalized_residual_bounded_inverse
#print axioms adjacent_geometric_of_normalized_residual
#print axioms geometric_of_bounded_raw_solution
#print axioms relative_firstOrderProduct
#print axioms normalized_residual_eq
end BTP.RelativeStability
