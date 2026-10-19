import RelativeLDUInverse

noncomputable section
open Filter
open scoped Topology
namespace BTP.RelativeStability
open BTP.GeneralStability

theorem relativeTriangularDerivative_injective {p q : ℕ}
    (a : Fin p → ℕ → ℝ) (b : Fin q → ℕ → ℝ)
    (ha : ∀ i n,0<a i n) (hb : ∀ i n,0<b i n) :
    Function.Injective (relativeTriangularDerivative a b ha hb) := by
  intro E F he
  apply Prod.ext
  · exact relativeProductDerivative_injective p a ha (congrArg Prod.fst he)
  · apply Prod.ext
    · have hd := congrArg (fun x : FullBand p q=>x.2.1) he
      exact hd
    · exact relativeProductDerivative_injective q b hb
        (congrArg (fun x : FullBand p q=>x.2.2) he)

/-- An analytic relative factor choice is the local inverse of actual
fixed-data multiplication. The proof also preserves a relative positive
margin of one half, without a uniform absolute lower bound on the base. -/
theorem relative_full_local_inverse {p q : ℕ}
    (a : Fin p → ℕ → ℝ) (d : ℕ → ℝ) (b : Fin q → ℕ → ℝ)
    (ha : ∀ i n,0<a i n) (hd : ∀ n,0<d n) (hb : ∀ i n,0<b i n)
    (S : RelativeLDUData (relativeFactorBase a) d (relativeFactorBase b))
    (hc : RelativeFullPositiveAnalyticChoice a d b ha hd hb) :
    ∃ g : FullBand p q → FullBand p q,
      AnalyticAt ℝ g 0 ∧ g 0=0 ∧
      (∀ᶠ E in 𝓝 (0 : FullBand p q),relativeFullProduct a d b ha hd hb (g E)=E) ∧
      (∀ᶠ h in 𝓝 (0 : FullBand p q),g (relativeFullProduct a d b ha hd hb h)=h) ∧
      (∀ᶠ E in 𝓝 (0 : FullBand p q),
        (∀ i n,a i n/2≤relativePerturbedFactor a (g E).1 i n) ∧
        (∀ i n,b i n/2≤relativePerturbedFactor b (g E).2.2 i n) ∧
        (∀ n,d n/2≤d n*(1+(g E).2.1 n)) ∧
        (∀ i n,n<p-i.val → relativePerturbedFactor a (g E).1 i n=a i n) ∧
        (∀ i n,n<q-i.val → relativePerturbedFactor b (g E).2.2 i n=b i n)) ∧
      ∃ K,∃ s ∈ 𝓝 (0 : FullBand p q),LipschitzOnWith K g s := by
  let A := relativeLDUProductDerivative (relativeFactorBase a) d (relativeFactorBase b)
    (relativeFactorBase_pos a ha) hd (relativeFactorBase_pos b hb) 0
  let B := relativeTriangularDerivative a b ha hb
  have hi : Function.Injective (A.comp B) :=
    (S.derivative_injective (relativeFactorBase_pos a ha) hd (relativeFactorBase_pos b hb)).comp
      (relativeTriangularDerivative_injective a b ha hb)
  obtain ⟨R,hR⟩ := relative_full_choice_derivative_rightInverse a d b ha hd hb hc
  have hs : Function.Surjective (A.comp B) := by
    intro E
    exact ⟨R E,congrArg (fun C : FullBand p q →L[ℝ] FullBand p q=>C E) hR⟩
  let D : FullBand p q ≃L[ℝ] FullBand p q :=
    ContinuousLinearEquiv.ofBijective (A.comp B)
      (LinearMap.ker_eq_bot.mpr hi) (LinearMap.range_eq_top.mpr hs)
  have hD : HasFDerivAt (relativeFullProduct a d b ha hd hb)
      (D : FullBand p q →L[ℝ] FullBand p q) 0 := relativeFullProduct_hasFDerivAt a d b ha hd hb
  obtain ⟨g,hga,hg0,hgR,hgL⟩ := BTP.AnalyticFactorization.analytic_local_inverse
    (analytic_relativeFullProduct a d b ha hd hb 0) D hD
  simp only [relativeFullProduct_zero] at hga hg0 hgR
  have hlim : Tendsto g (𝓝 (0 : FullBand p q)) (𝓝 0) := by
    simpa only [ContinuousAt,hg0] using hga.continuousAt
  have hsmall : ∀ᶠ E in 𝓝 (0 : FullBand p q),‖g E‖<1/2 := by
    simpa only [Metric.mem_ball,dist_zero_right] using
      hlim.eventually (Metric.ball_mem_nhds (0 : FullBand p q) (by norm_num : (0:ℝ)<1/2))
  refine ⟨g,hga,hg0,hgR,hgL,?_,hga.hasStrictFDerivAt.exists_lipschitzOnWith⟩
  filter_upwards [hsmall] with E hE
  have hLn : ‖(g E).1‖≤‖g E‖ := norm_fst_le _
  have hDn : ‖(g E).2.1‖≤‖g E‖ := (norm_fst_le _).trans (norm_snd_le _)
  have hUn : ‖(g E).2.2‖≤‖g E‖ := (norm_snd_le _).trans (norm_snd_le _)
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i n
    have hh := (abs_le.mp ((factorVariation_abs_le (g E).1 i n).trans hLn)).1
    have hm := mul_le_mul_of_nonneg_left
      (show (1:ℝ)/2≤1+factorVariation p i.val (g E).1 n by linarith) (le_of_lt (ha i n))
    simpa only [relativePerturbedFactor,div_eq_mul_inv,one_mul] using hm
  · intro i n
    have hh := (abs_le.mp ((factorVariation_abs_le (g E).2.2 i n).trans hUn)).1
    have hm := mul_le_mul_of_nonneg_left
      (show (1:ℝ)/2≤1+factorVariation q i.val (g E).2.2 n by linarith) (le_of_lt (hb i n))
    simpa only [relativePerturbedFactor,div_eq_mul_inv,one_mul] using hm
  · intro n
    have hh := (abs_le.mp ((BTP.Stability.boundedSequence_abs_le (g E).2.1 n).trans hDn)).1
    have hm := mul_le_mul_of_nonneg_left
      (show (1:ℝ)/2≤1+(g E).2.1 n by linarith) (le_of_lt (hd n))
    simpa only [div_eq_mul_inv,one_mul] using hm
  · exact fun i n hn=>relativePerturbedFactor_fixed a (g E).1 i n hn
  · exact fun i n hn=>relativePerturbedFactor_fixed b (g E).2.2 i n hn

#print axioms relative_full_local_inverse
end BTP.RelativeStability
