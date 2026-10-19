import FreeGeneralCriterion
import AnalyticPositiveFactors

/-! Complete analytic stability for arbitrary lower bandwidth with all
initial factor entries free. The factors are multiplied in their actual
left-to-right order. Their row-zero values are unused dummy coordinates;
the first variation coordinate changes the entry in row one. -/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace BTP.GeneralStability

def freePerturbedFactors {p : ℕ} (a h : Fin p → Seq) (i : Fin p) (n : ℕ) : ℝ :=
  a i n + initialExtension 1 (h i) n

/-- An analytic local choice in the uniform factor and band norms,
through the prescribed PBF, with all actual initial entries free. -/
def FreePositiveAnalyticChoice {p : ℕ} (a : Fin p → Seq) : Prop :=
  ∃ g : LowerBand p → FactorVariations p,
    AnalyticAt ℝ g (lowerProductBand a) ∧ g (lowerProductBand a) = 0 ∧
    (∀ᶠ T in 𝓝 (lowerProductBand a), freeProduct a (g T) = T ∧
      ∀ i n, 1 ≤ n → 0 < freePerturbedFactors a (g T) i n)

/-- The weaker differentiable local choice appearing as condition (3)
in the manuscript. Differentiability is only required at the base matrix. -/
def FreePositiveDifferentiableChoice {p : ℕ} (a : Fin p → Seq) : Prop :=
  ∃ g : LowerBand p → FactorVariations p,
    DifferentiableAt ℝ g (lowerProductBand a) ∧ g (lowerProductBand a) = 0 ∧
    (∀ᶠ T in 𝓝 (lowerProductBand a), freeProduct a (g T) = T ∧
      ∀ i n, 1 ≤ n → 0 < freePerturbedFactors a (g T) i n)

theorem free_differentiable_choice_implies_pairs (p : ℕ) (a : Fin p → Seq)
    (α : ℝ) (hα : 0 < α) (ha : ∀ i n, α ≤ a i n)
    (h : FreePositiveDifferentiableChoice a) : FreePairCondition p a := by
  obtain ⟨g,hg,hg0,hchoice⟩ := h
  have hright : ∀ᶠ T in 𝓝 (freeProduct a 0), freeProduct a (g T) = T := by
    simpa only [freeProduct_zero] using hchoice.mono (fun _ h => h.1)
  have hga : g (freeProduct a 0) = 0 := by simpa only [freeProduct_zero] using hg0
  have hgd : HasFDerivAt g (fderiv ℝ g (freeProduct a 0)) (freeProduct a 0) := by
    simpa only [freeProduct_zero] using hg.hasFDerivAt
  have hid := BTP.AnalyticFactorization.derivative_right_inverse_of_section
    (freeProduct_hasFDerivAt p a) hgd hga hright
  exact (freeProductDerivative_rightInverse_iff_pairs p a α hα ha).mp ⟨_,hid⟩

theorem free_analytic_choice_of_pairs (p : ℕ) (a : Fin p → Seq)
    (α : ℝ) (hα : 0 < α) (ha : ∀ i n, α ≤ a i n)
    (hpair : FreePairCondition p a) : FreePositiveAnalyticChoice a := by
  obtain ⟨R,hR⟩ := (freeProductDerivative_rightInverse_iff_pairs p a α hα ha).mpr hpair
  obtain ⟨g,hg,hg0,hright⟩ := BTP.AnalyticFactorization.analytic_local_section
    (analytic_freeProduct p a 0) (freeProductDerivative p a) R
    (freeProduct_hasFDerivAt p a) hR
  simp only [freeProduct_zero] at hg hg0 hright
  have hlim : Tendsto g (𝓝 (lowerProductBand a)) (𝓝 0) := by
    simpa only [ContinuousAt,hg0] using hg.continuousAt
  have hsmall : ∀ᶠ T in 𝓝 (lowerProductBand a), ‖g T‖ < α := by
    simpa only [Metric.mem_ball,dist_zero_right] using
      hlim.eventually (Metric.ball_mem_nhds (0 : FactorVariations p) hα)
  refine ⟨g,hg,hg0,?_⟩
  filter_upwards [hright,hsmall] with T hprod hnorm
  refine ⟨hprod,?_⟩
  intro i n _
  have he := (initialExtension_abs_le 1 (g T i) n).trans (norm_le_pi_norm (g T) i)
  have hlo := (abs_le.mp he).1
  have hbase := ha i n
  dsimp [freePerturbedFactors]
  linarith

/-- The main arbitrary-bandwidth equivalence with variable initial
entries. Both directions concern the derivative of the actual matrix
product, rather than a separately postulated linear operator. -/
theorem free_initial_positive_factorization_iff_pairs (p : ℕ) (a : Fin p → Seq)
    (α : ℝ) (hα : 0 < α) (ha : ∀ i n, α ≤ a i n) :
    FreePositiveAnalyticChoice a ↔ FreePairCondition p a := by
  constructor
  · rintro ⟨g,hg,hg0,hchoice⟩
    exact free_differentiable_choice_implies_pairs p a α hα ha
      ⟨g,hg.differentiableAt,hg0,hchoice⟩
  · exact free_analytic_choice_of_pairs p a α hα ha

theorem free_initial_differentiable_factorization_iff_pairs (p : ℕ) (a : Fin p → Seq)
    (α : ℝ) (hα : 0 < α) (ha : ∀ i n, α ≤ a i n) :
    FreePositiveDifferentiableChoice a ↔ FreePairCondition p a := by
  constructor
  · exact free_differentiable_choice_implies_pairs p a α hα ha
  · intro hpair
    obtain ⟨g,hg,hg0,hchoice⟩ := free_analytic_choice_of_pairs p a α hα ha hpair
    exact ⟨g,hg.differentiableAt,hg0,hchoice⟩

/-- Geometric products beginning at the first actual row on which the
shifted quotient is defined. This form uses the manuscript's row index. -/
def GeometricFromRow (w : ℕ → ℝ) (first : ℕ) : Prop :=
  ∃ C ρ : ℝ, 1 ≤ C ∧ 0 < ρ ∧ ρ < 1 ∧
    ∀ n N, first ≤ n → (∏ t ∈ Finset.range N, w (n+t)) ≤ C*ρ^N

theorem geometric_reindex_from_row (w : ℕ → ℝ) (d : ℕ) :
    BTP.FreeScalar.Geometric (fun n => w (n+d)) ↔ GeometricFromRow w (d+1) := by
  constructor
  · rintro ⟨C,ρ,hC,hρ,hρ1,hprod⟩
    refine ⟨C,ρ,hC,hρ,hρ1,?_⟩
    intro n N hn
    have h := hprod (n-d-1) N
    have he : BTP.Stability.blockProduct (fun k => w (k+d)) (n-d-1) N =
        ∏ t ∈ Finset.range N, w (n+t) := by
      unfold BTP.Stability.blockProduct
      apply Finset.prod_congr rfl
      intro t _
      change w ((n-d-1+t+1)+d) = w (n+t)
      congr 1
      omega
    exact he ▸ h
  · rintro ⟨C,ρ,hC,hρ,hρ1,hprod⟩
    refine ⟨C,ρ,hC,hρ,hρ1,?_⟩
    intro s N
    have h := hprod (s+d+1) N (by omega)
    simpa only [BTP.Stability.blockProduct,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using h

def ManuscriptFreePairCondition (p : ℕ) (a : Fin p → Seq) : Prop :=
  ∀ i j : Fin p, i < j →
    GeometricFromRow (fun n => a i n/a j (n-(j.val-i.val))) (j.val-i.val+1) ∨
    GeometricFromRow (fun n => (a i n/a j (n-(j.val-i.val)))⁻¹) (j.val-i.val+1)

theorem freePairCondition_iff_manuscript (p : ℕ) (a : Fin p → Seq) :
    FreePairCondition p a ↔ ManuscriptFreePairCondition p a := by
  have hp (i j : Fin p) :
      BTP.FreeScalar.Geometric (fun n => a i (n+(j.val-i.val))/a j n) ↔
        GeometricFromRow (fun n => a i n/a j (n-(j.val-i.val))) (j.val-i.val+1) := by
    simpa only [Nat.add_sub_cancel] using geometric_reindex_from_row
      (fun n => a i n/a j (n-(j.val-i.val))) (j.val-i.val)
  have hm (i j : Fin p) :
      BTP.FreeScalar.Geometric (fun n => (a i (n+(j.val-i.val))/a j n)⁻¹) ↔
        GeometricFromRow (fun n => (a i n/a j (n-(j.val-i.val)))⁻¹) (j.val-i.val+1) := by
    simpa only [Nat.add_sub_cancel] using geometric_reindex_from_row
      (fun n => (a i n/a j (n-(j.val-i.val)))⁻¹) (j.val-i.val)
  constructor
  · intro h i j hij
    exact (or_congr (hp i j) (hm i j)).mp (h i j hij)
  · intro h i j hij
    exact (or_congr (hp i j) (hm i j)).mpr (h i j hij)

theorem free_initial_positive_factorization_iff_manuscript (p : ℕ) (a : Fin p → Seq)
    (α : ℝ) (hα : 0 < α) (ha : ∀ i n, α ≤ a i n) :
    FreePositiveAnalyticChoice a ↔ ManuscriptFreePairCondition p a := by
  rw [free_initial_positive_factorization_iff_pairs p a α hα ha,
    freePairCondition_iff_manuscript]

theorem free_initial_differentiable_factorization_iff_manuscript (p : ℕ) (a : Fin p → Seq)
    (α : ℝ) (hα : 0 < α) (ha : ∀ i n, α ≤ a i n) :
    FreePositiveDifferentiableChoice a ↔ ManuscriptFreePairCondition p a := by
  rw [free_initial_differentiable_factorization_iff_pairs p a α hα ha,
    freePairCondition_iff_manuscript]

/-- The same analytic choice is Lipschitz on a neighborhood in the
uniform norms used for both factors and band coefficients. -/
theorem free_positive_choice_with_lipschitz (p : ℕ) (a : Fin p → Seq)
    (α : ℝ) (hα : 0 < α) (ha : ∀ i n, α ≤ a i n)
    (hpair : FreePairCondition p a) :
    ∃ g : LowerBand p → FactorVariations p,
      AnalyticAt ℝ g (lowerProductBand a) ∧ g (lowerProductBand a) = 0 ∧
      (∀ᶠ T in 𝓝 (lowerProductBand a), freeProduct a (g T) = T ∧
        ∀ i n, 1 ≤ n → 0 < freePerturbedFactors a (g T) i n) ∧
      ∃ K, ∃ s ∈ 𝓝 (lowerProductBand a), LipschitzOnWith K g s := by
  obtain ⟨g,hg,hg0,hchoice⟩ := free_analytic_choice_of_pairs p a α hα ha hpair
  exact ⟨g,hg,hg0,hchoice,hg.hasStrictFDerivAt.exists_lipschitzOnWith⟩

#print axioms free_initial_positive_factorization_iff_pairs
#print axioms free_initial_differentiable_factorization_iff_pairs
#print axioms free_initial_positive_factorization_iff_manuscript
#print axioms free_positive_choice_with_lipschitz

end BTP.GeneralStability
