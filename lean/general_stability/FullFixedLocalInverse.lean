import FullFreeCriterion

/-! Local uniqueness, uniform positive margins, and Lipschitz continuity
for the complete fixed-initial-entry multiplication map. -/
noncomputable section
open Filter
open scoped Topology
namespace BTP.GeneralStability
open BTP.Stability.BandLDU

theorem fixedTriangularDerivative_injective {p q : ℕ}
    (a : Fin p → Seq) (b : Fin q → Seq)
    (ha : ∀ i n,a i n≠0) (hb : ∀ j n,b j n≠0) :
    Function.Injective (fixedTriangularDerivative a b) := by
  intro E F he
  apply Prod.ext
  · exact fixedProductDerivative_injective p a ha (congrArg Prod.fst he)
  · apply Prod.ext
    · have hdiag : (fixedTriangularDerivative a b E).2.1=(fixedTriangularDerivative a b F).2.1 :=
        congrArg (fun x : FullBand p q => x.2.1) he
      exact hdiag
    · exact fixedProductDerivative_injective q b hb
        (congrArg (fun x : FullBand p q => x.2.2) he)

/-- The positive analytic choice can be chosen to be the actual local
inverse of multiplication. Its entries stay uniformly above α/2. -/
theorem full_fixed_local_inverse {p q : ℕ}
    (a : Fin p → Seq) (d : Seq) (b : Fin q → Seq)
    {α M : ℝ} (hα : 0<α) (hM : 0≤M)
    (ha : ∀ i n,α≤a i n) (hb : ∀ j n,α≤b j n) (hd : ∀ n,α≤d n)
    (haM : ∀ i n,|a i n|≤M) (hbM : ∀ j n,|b j n|≤M)
    (hchoice : FullFixedPositiveAnalyticChoice a d b) :
    ∃ g : FullBand p q → FullBand p q,
      AnalyticAt ℝ g (lduProduct (factorBase a d b)) ∧
      g (lduProduct (factorBase a d b))=0 ∧
      (∀ᶠ T in 𝓝 (lduProduct (factorBase a d b)),fixedFullProduct a d b (g T)=T) ∧
      (∀ᶠ h in 𝓝 (0 : FullBand p q),g (fixedFullProduct a d b h)=h) ∧
      (∀ᶠ T in 𝓝 (lduProduct (factorBase a d b)),
        (∀ i n,α/2≤perturbedFactors a (g T).1 i n) ∧
        (∀ j n,α/2≤perturbedFactors b (g T).2.2 j n) ∧
        (∀ n,α/2≤(d+(g T).2.1) n)) ∧
      ∃ K,∃ s ∈ 𝓝 (lduProduct (factorBase a d b)),LipschitzOnWith K g s := by
  let D := (lduProductDerivative (factorBase a d b)).comp (fixedTriangularDerivative a b)
  have hDinj : Function.Injective D :=
    (factorBase_derivative_injective a d b
      (fun n => ne_of_gt (lt_of_lt_of_le hα (hd n))) hM haM hbM).comp
      (fixedTriangularDerivative_injective a b
        (fun i n => ne_of_gt (lt_of_lt_of_le hα (ha i n)))
        (fun j n => ne_of_gt (lt_of_lt_of_le hα (hb j n))))
  obtain ⟨R,hR⟩ := full_fixed_choice_derivative_rightInverse a d b hchoice
  have hDsurj : Function.Surjective D := by
    intro E
    exact ⟨R E,congrArg (fun C : FullBand p q →L[ℝ] FullBand p q => C E) hR⟩
  let J : FullBand p q ≃L[ℝ] FullBand p q :=
    ContinuousLinearEquiv.ofBijective D (LinearMap.ker_eq_bot.mpr hDinj)
      (LinearMap.range_eq_top.mpr hDsurj)
  have hder : HasFDerivAt (fixedFullProduct a d b)
      (J : FullBand p q →L[ℝ] FullBand p q) 0 := fixedFullProduct_hasFDerivAt a d b
  obtain ⟨g,hg,hg0,hgR,hgL⟩ := BTP.AnalyticFactorization.analytic_local_inverse
    (analytic_fixedFullProduct a d b 0) J hder
  simp only [fixedFullProduct_zero] at hg hg0 hgR
  have hlim : Tendsto g (𝓝 (lduProduct (factorBase a d b))) (𝓝 0) := by
    simpa only [ContinuousAt,hg0] using hg.continuousAt
  have hsmall : ∀ᶠ T in 𝓝 (lduProduct (factorBase a d b)),‖g T‖<α/2 := by
    simpa only [Metric.mem_ball,dist_zero_right] using
      hlim.eventually (Metric.ball_mem_nhds (0 : FullBand p q) (by linarith : 0<α/2))
  refine ⟨g,hg,hg0,hgR,hgL,?_,hg.hasStrictFDerivAt.exists_lipschitzOnWith⟩
  filter_upwards [hsmall] with T hT
  have hLn : ‖(g T).1‖≤‖g T‖ := norm_fst_le _
  have hDn : ‖(g T).2.1‖≤‖g T‖ := (norm_fst_le _).trans (norm_snd_le _)
  have hUn : ‖(g T).2.2‖≤‖g T‖ := (norm_snd_le _).trans (norm_snd_le _)
  refine ⟨?_,?_,?_⟩
  · intro i n
    have he := (perturbedFactors_abs_sub_le a (g T).1 i n).trans hLn
    have hl := (abs_le.mp he).1
    have ha0 := ha i n
    linarith
  · intro j n
    have he := (perturbedFactors_abs_sub_le b (g T).2.2 j n).trans hUn
    have hl := (abs_le.mp he).1
    have hb0 := hb j n
    linarith
  · intro n
    have he := (BTP.Stability.boundedSequence_abs_le (g T).2.1 n).trans hDn
    have hl := (abs_le.mp he).1
    have hd0 := hd n
    change α/2≤d n+(g T).2.1 n
    linarith

#print axioms full_fixed_local_inverse
end BTP.GeneralStability
