import FactorOrderBridge
import InverseDominance

/-! Full-band positive factorization from the manuscript's actual
adjacent and crossed geometric conditions, in arbitrary finite widths. -/
noncomputable section
open Finset Filter
open scoped Topology BigOperators
namespace BTP.GeneralStability
open BTP BTP.SemiInfinite BTP.Stability BTP.Stability.BandLDU

theorem reversedEntries_positive {p : ℕ} (a : Fin p → Seq)
    {α : ℝ} (hα : 0<α) (ha : ∀ i n, α≤a i n) (k : ℕ) (hk : k<p) (n : ℕ) :
    0<reversedEntries a k n := by
  simp only [reversedEntries,hk,↓reduceDIte]
  exact lt_of_lt_of_le hα (ha _ _)

theorem reversedEntries_lower {p : ℕ} (a : Fin p → Seq)
    {α β : ℝ} (hβα : β≤α) (ha : ∀ i n, α≤a i n)
    (k : ℕ) (hk : k<p) (n : ℕ) : β≤reversedEntries a k n := by
  simp only [reversedEntries,hk,↓reduceDIte]
  exact hβα.trans (ha _ _)

theorem reversedEntries_upper {p : ℕ} (a : Fin p → Seq)
    {M : ℝ} (ha : ∀ i n, |a i n|≤M)
    (k : ℕ) (hk : k<p) (n : ℕ) : |reversedEntries a k n|≤M := by
  simp only [reversedEntries,hk,↓reduceDIte]
  exact ha _ _

theorem reversed_adjacent_same_row {p : ℕ} (a : Fin (p+1) → Seq)
    {α M : ℝ} (hα : 0<α) (ha : ∀ i n, α≤a i n) (haM : ∀ i n, |a i n|≤M)
    (hg : ManuscriptAdjacentGeometric (p+1) a) :
    ∀ i<p, GeometricDecay (fun n => reversedEntries a (i+1) n/reversedEntries a i n) := by
  intro i hi
  let j := p-i-1
  have hj : j+1<p+1 := by dsimp [j]; omega
  have he1 : (Fin.rev (⟨i+1,by omega⟩ : Fin (p+1)))=(⟨j,by omega⟩ : Fin (p+1)) := by
    apply Fin.ext
    simp only [Fin.rev]
    dsimp [j]
    omega
  have he0 : (Fin.rev (⟨i,by omega⟩ : Fin (p+1)))=(⟨j+1,hj⟩ : Fin (p+1)) := by
    apply Fin.ext
    simp only [Fin.rev]
    dsimp [j]
    omega
  have hh := geometric_same_row_of_shifted (a ⟨j,by omega⟩) (a ⟨j+1,hj⟩) hα
    (fun n => lt_of_lt_of_le hα (ha _ n)) (ha _)
    (fun n => (le_abs_self _).trans (haM _ n)) (hg j hj)
  simpa only [reversedEntries,show i+1<p+1 by omega,show i<p+1 by omega,
    ↓reduceDIte,he1,he0] using hh

theorem reversedEntries_zero {p : ℕ} (a : Fin (p+1) → Seq) (n : ℕ) :
    reversedEntries a 0 n=a (Fin.last p) n := by
  simp [reversedEntries,Fin.rev,Fin.last]

/-- The full geometric criterion gives a genuine analytic normalized
LDU map, without assuming any LDU inverse or analytic dependence. -/
theorem analytic_ldu_of_adjacent_cross (p q : ℕ)
    (a : Fin (p+1) → Seq) (d : Seq) (b : Fin (q+1) → Seq)
    {α M : ℝ} (hα : 0<α) (hM : 0≤M)
    (ha : ∀ i n, α≤a i n) (hb : ∀ j n, α≤b j n) (hd : ∀ n, α≤d n)
    (haM : ∀ i n, |a i n|≤M) (hbM : ∀ j n, |b j n|≤M)
    (hga : ManuscriptAdjacentGeometric (p+1) a)
    (hgb : ManuscriptAdjacentGeometric (q+1) b)
    (hcross : GeometricDecay (fun n => a (Fin.last p) n*b (Fin.last q) n)) :
    AnalyticLDUSection (factorBase a d b) := by
  let ar := reversedEntries a
  let br := reversedEntries b
  have har : ∀ i<p+1, ∀ n, 0<n → min α 1≤ar i n :=
    fun i hi n _ => reversedEntries_lower a (min_le_left _ _) ha i hi n
  have hbr : ∀ i<q+1, ∀ n, 0<n → min α 1≤br i n :=
    fun i hi n _ => reversedEntries_lower b (min_le_left _ _) hb i hi n
  have harM : ∀ i<p+1, ∀ n, 0<n → |ar i n|≤M :=
    fun i hi n _ => reversedEntries_upper a haM i hi n
  have hbrM : ∀ i<q+1, ∀ n, 0<n → |br i n|≤M :=
    fun i hi n _ => reversedEntries_upper b hbM i hi n
  have hc : GeometricDecay (fun n => ar 0 n*br 0 n) := by
    simpa only [ar,br,reversedEntries_zero] using hcross
  have hrows := actual_joint_rows_bounded_of_geometric ar br p q
    (fun i hi n => reversedEntries_positive a hα ha i (by omega) n)
    (fun i hi n => reversedEntries_positive b hα hb i (by omega) n)
    (reversed_adjacent_same_row a hα ha haM hga)
    (reversed_adjacent_same_row b hα hb hbM hgb) hc
  have hdne : ∀ n, d n≠0 := fun n => ne_of_gt (lt_of_lt_of_le hα (hd n))
  have hdinv : ∀ n, |(d n)⁻¹|≤1/α := by
    intro n
    rw [abs_of_pos (inv_pos.mpr (lt_of_lt_of_le hα (hd n))),one_div]
    exact inv_anti₀ hα (hd n)
  have he := (actual_ldu_analytic_iff_row_bound ar br p q d hdne
    (lt_min hα zero_lt_one) (min_le_right _ _) hM (by positivity)
    har hbr harM hbrM hdinv).mpr hrows
  rw [reversed_factor_base] at he
  exact he

/-- Full-band fixed-initial-entry sufficiency for arbitrary lower and
upper widths. Every matrix in one neighborhood receives positive factors
with their initial entries unchanged. -/
theorem full_fixed_positive_of_geometric (p q : ℕ)
    (a : Fin (p+1) → Seq) (d : Seq) (b : Fin (q+1) → Seq)
    {α M : ℝ} (hα : 0<α) (hM : 0≤M)
    (ha : ∀ i n, α≤a i n) (hb : ∀ j n, α≤b j n) (hd : ∀ n, α≤d n)
    (haM : ∀ i n, |a i n|≤M) (hbM : ∀ j n, |b j n|≤M)
    (hga : ManuscriptAdjacentGeometric (p+1) a)
    (hgb : ManuscriptAdjacentGeometric (q+1) b)
    (hcross : GeometricDecay (fun n => a (Fin.last p) n*b (Fin.last q) n)) :
    FullFixedPositiveAnalyticChoice a d b := by
  exact full_fixed_positive_of_ldu_and_adjacent a d b hα ha hd hb hga hgb
    (analytic_ldu_of_adjacent_cross p q a d b hα hM ha hb hd haM hbM hga hgb hcross)

#print axioms analytic_ldu_of_adjacent_cross
#print axioms full_fixed_positive_of_geometric
end BTP.GeneralStability
