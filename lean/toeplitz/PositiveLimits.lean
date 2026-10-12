import GlobalConstruction

/-! # Positive inverse-minor limits imply a global positive factorization

The hypotheses refer to the unique compatible Metelmann data supplied by the
matrix theory. No global positive factorization is assumed.
-/
open Matrix Finset Filter
open scoped Topology
noncomputable section
namespace BTP.SemiInfinite
open Extraction

/-- The actual decreasing inverse-minor limit (order k+1). -/
def inverseMinorLimit (a : Entries) (p k : ℕ) : ℝ := ⨅ n, inverseMinorRatio a p k n

theorem inverseMinorLimit_eq_seriesEndpoint {p k : ℕ} {a : Entries}
    (ha : Metelmann p a) (hk : k + 1 < p) :
    inverseMinorLimit a p k = seriesEndpoint a (k + 1) := by
  unfold inverseMinorLimit seriesEndpoint endpoint
  congr 1
  funext n
  exact inverseMinorRatio_eq_convergent ha hk n

theorem metelmann_product_outer {p : ℕ} {a : Entries} (ha : Metelmann p a) :
    ∀ n, p ≤ n → 0 < productEntries a p n (n - p) := by
  intro n hn
  simp only [productEntries, Nat.sub_le, ite_true, show n - (n - p) = p by omega]
  exact entry_diag_pos a p n hn (fun j hj t _ ht => ha.2 j hj t ht)

theorem metelmann_signedInverse (p : ℕ) (a : Entries) :
    SignedInverse (productEntries a p) (inverseEntries a p) := by
  intro d
  rw [product_finite]
  ext i j
  exact signed_inverse_section d p a i j

/-- A single open neighborhood works for every row and every extraction stage. -/
theorem all_small_parameters_extend {p : ℕ} (hp : 0 < p) {a : Entries}
    (ha : Metelmann p a)
    (hs : ∀ k, 0 < k → k < p → Summable (adjacentTerm a k)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ u : Parameters p, ‖u‖ < ε → (∀ c, 0 < u c) →
      ∃ b : Entries, Positive p b ∧ SameProduct p b a ∧
        (∀ j < p, ∀ n, 0 < n → n ≤ j → b j n = freeValue p u j n) := by
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp (planned_windows_positive ha hs)
  refine ⟨ε, hε, ?_⟩
  intro u hu hupos
  have hw := he (by simpa using hu)
  obtain ⟨b, hb, hinit, hprod⟩ := construct_from_planned_windows p (inverseEntries a p) u
    hupos hw p hp 0 (by omega) (productEntries a p) (inverseEntries a p)
    (fun d => product_unit d a p) (fun d => product_band d a p)
    (metelmann_product_outer ha) (metelmann_signedInverse p a)
    (fun n j hj => (plannedInverse_initial _ _ _ n j hj).symm)
  refine ⟨b, hb, ?_, hinit⟩
  intro d
  rw [hprod, product_finite]

theorem summable_series_give_PBF {p : ℕ} (hp : 0 < p) {a : Entries}
    (ha : Metelmann p a)
    (hs : ∀ k, 0 < k → k < p → Summable (adjacentTerm a k)) : HasPBF p a := by
  obtain ⟨ε, hε, he⟩ := all_small_parameters_extend hp ha hs
  let u : Parameters p := fun _ => ε / 2
  have hn : ‖u‖ ≤ ε / 2 := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro c
    simp only [u, Real.norm_eq_abs, abs_of_pos (show 0 < ε / 2 by positivity)]
    exact le_rfl
  obtain ⟨b, hb, hsame, _⟩ := he u (lt_of_le_of_lt hn (by linarith))
    (fun _ => by dsimp [u]; positivity)
  exact ⟨b, hb, hsame⟩

/-- The semi-infinite lower sufficiency theorem, using actual inverse minors. -/
theorem positive_limits_give_PBF {p : ℕ} (hp : 0 < p) {a : Entries}
    (ha : Metelmann p a)
    (hlim : ∀ k, k + 1 < p → 0 < inverseMinorLimit a p k) : HasPBF p a := by
  apply summable_series_give_PBF hp ha
  intro k hk hkp
  apply (seriesEndpoint_pos_iff ha hk hkp).mp
  have he := hlim (k - 1) (by omega)
  rw [inverseMinorLimit_eq_seriesEndpoint ha (by omega), show k - 1 + 1 = k by omega] at he
  exact he

/-- Sections of LDU. Upper factors are transposes of unit lower factors. -/
def triangularSections (p q : ℕ) (a c : Entries) (D : ℕ → ℝ) (d : ℕ) :
    Matrix (Fin d) (Fin d) ℝ :=
  lowerProduct d a p * Matrix.diagonal (fun i : Fin d => D i.val) *
    (lowerProduct d c q).transpose

def HasTwoSidedPBF (p q : ℕ) (a c : Entries) (D : ℕ → ℝ) : Prop :=
  (∀ n, 0 < D n) ∧ ∃ b e : Entries, Positive p b ∧ Positive q e ∧
    ∀ d, triangularSections p q b e D d = triangularSections p q a c D d

/-- The p+q-2 strictly positive limits give ONE PBF of ALL leading sections. -/
theorem positive_limits_give_two_sided_PBF {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {a c : Entries} {D : ℕ → ℝ}
    (ha : Metelmann p a) (hc : Metelmann q c) (hD : ∀ n, 0 < D n)
    (hminus : ∀ k, k + 1 < p → 0 < inverseMinorLimit a p k)
    (hplus : ∀ k, k + 1 < q → 0 < inverseMinorLimit c q k) :
    HasTwoSidedPBF p q a c D := by
  obtain ⟨b, hb, hbprod⟩ := positive_limits_give_PBF hp ha hminus
  obtain ⟨e, he, heprod⟩ := positive_limits_give_PBF hq hc hplus
  refine ⟨hD, b, e, hb, he, ?_⟩
  intro d
  unfold triangularSections
  rw [hbprod d, heprod d]

#print axioms all_small_parameters_extend
#print axioms positive_limits_give_PBF
#print axioms positive_limits_give_two_sided_PBF
end BTP.SemiInfinite
