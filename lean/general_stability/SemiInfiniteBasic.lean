import SeriesLimits

/-! # Semi-infinite matrices interpreted through their finite leading sections

The factors here have ONE array of entries, shared by every dimension.
Quantifier order is intentional: global factorization is `∃ b, ∀ d`,
not the weaker `∀ d, ∃ b`.
-/

open Matrix Finset Filter
open scoped Topology
noncomputable section
namespace BTP.SemiInfinite

/-- The prescribed initial zeros and the positive tails, in right-to-left order. -/
def Metelmann (p : ℕ) (a : Entries) : Prop :=
  (∀ j < p, ∀ n, 0 < n → n ≤ j → a j n = 0) ∧
  (∀ j < p, ∀ n, j < n → 0 < a j n)

/-- All subdiagonal entries in all factors are positive. -/
def Positive (p : ℕ) (b : Entries) : Prop :=
  ∀ j < p, ∀ n, 0 < n → 0 < b j n

/-- Exact equality of every finite leading section. -/
def SameProduct (p : ℕ) (a b : Entries) : Prop :=
  ∀ d, lowerProduct d a p = lowerProduct d b p

/-- A single positive factorization valid in every row. -/
def HasPBF (p : ℕ) (a : Entries) : Prop :=
  ∃ b : Entries, Positive p b ∧ SameProduct p b a

theorem Metelmann.finite {p : ℕ} {a : Entries} (h : Metelmann p a) (d : ℕ) :
    InverseBounds.Metelmann d p a := by
  exact ⟨h.1, fun j hj n hnd hn => h.2 j hj n hn⟩

theorem Positive.finite {p : ℕ} {b : Entries} (h : Positive p b) (d : ℕ) :
    InverseBounds.PositiveFactors d p b := by
  exact fun j hj n hn _ => h j hj n hn

/-- Finite sections of a product agree because its entries are local formulas. -/
theorem product_compatible {d D p : ℕ} (a : Entries) (h : d ≤ D) :
    (lowerProduct D a p).submatrix (Fin.castLE h) (Fin.castLE h) =
      lowerProduct d a p := by
  ext i j
  simp only [Matrix.submatrix_apply, lowerProduct_entry, Fin.val_castLE]

/-- Equality of every finite section is exactly equality of the semi-infinite
matrix entries already defined in the finite extraction module. -/
theorem sameProduct_iff_entries (p : ℕ) (a b : Entries) :
    SameProduct p a b ↔ Extraction.productEntries a p = Extraction.productEntries b p := by
  constructor
  · intro h
    funext i j
    let d := max i j + 1
    have hi : i < d := by dsimp [d]; omega
    have hj : j < d := by dsimp [d]; omega
    have e := congrArg (fun M : Matrix (Fin d) (Fin d) ℝ => M ⟨i, hi⟩ ⟨j, hj⟩) (h d)
    simpa only [lowerProduct_entry, Extraction.productEntries] using e
  · intro h d
    rw [← Extraction.product_finite, ← Extraction.product_finite, h]

/-- Bandwidth one needs no limiting conditions. -/
theorem hasPBF_one {a : Entries} (ha : Metelmann 1 a) : HasPBF 1 a := by
  refine ⟨a, ?_, fun _ => rfl⟩
  intro j hj n hn
  have : j = 0 := by omega
  subst j
  exact ha.2 0 (by omega) n hn

/-- The cumulative products π_j of the manuscript. -/
def cumulative (a : Entries) (j n : ℕ) : ℝ :=
  ∏ t ∈ Ico j n, a j (t + 1)

theorem cumulative_pos {p : ℕ} {a : Entries} (ha : Metelmann p a)
    {j : ℕ} (hj : j < p) (n : ℕ) : 0 < cumulative a j n := by
  apply prod_pos
  intro t ht
  exact ha.2 j hj (t + 1) (by have := mem_Ico.mp ht; omega)

/-- The summation variable starts at zero: this is r_k(k+n) in the paper. -/
def adjacentTerm (a : Entries) (k n : ℕ) : ℝ :=
  cumulative a k (k + n) / cumulative a (k - 1) (k + n)

theorem adjacentTerm_pos {p : ℕ} {a : Entries} (ha : Metelmann p a)
    {k : ℕ} (hk : 0 < k) (hkp : k < p) (n : ℕ) : 0 < adjacentTerm a k n := by
  exact div_pos (cumulative_pos ha hkp _) (cumulative_pos ha (by omega) _)

/-- Limits computed from the actual adjacent Metelmann series. -/
def seriesEndpoint (a : Entries) (k : ℕ) : ℝ := endpoint (adjacentTerm a k)

theorem seriesEndpoint_pos_iff {p : ℕ} {a : Entries} (ha : Metelmann p a)
    {k : ℕ} (hk : 0 < k) (hkp : k < p) :
    0 < seriesEndpoint a k ↔ Summable (adjacentTerm a k) :=
  endpoint_pos_iff_summable (adjacentTerm_pos ha hk hkp)

/-- The global extraction recurrence is well-defined before any choice of a
finite section. Positivity of its solution gives a positive factor in ALL rows. -/
theorem global_extraction {m : ℕ} (hm : 2 ≤ m)
    (F : Extraction.NatMatrix) (θ : ℕ → ℝ)
    (hF : ∀ d, Extraction.UnitLower d F)
    (hb : ∀ d, Extraction.Bandwidth d m F)
    (hext : ∀ n, m ≤ n → 0 < F n (n - m))
    (hθ : ∀ n, 0 < n → n < m → 0 < θ n)
    (hφ : ∀ n, 0 < Extraction.canonicalSequence m (by omega) F θ n) :
    ∃ a : ℕ → ℝ, ∃ H : Extraction.NatMatrix,
      (∀ n, 0 < n → 0 < a n) ∧
      (∀ n, 0 < n → n < m → a n = θ n) ∧
      (∀ d, Extraction.UnitLower d H) ∧
      (∀ d, Extraction.Bandwidth d (m - 1) H) ∧
      (∀ d, bidiagonal d a * Extraction.finiteMatrix d H = Extraction.finiteMatrix d F) := by
  let φ := Extraction.canonicalSequence m (by omega) F θ
  let a := fun n => φ (n - 1) / φ n
  let H := Extraction.remainder a F
  refine ⟨a, H, ?_, ?_, ?_, ?_, ?_⟩
  · intro n _; exact div_pos (hφ _) (hφ _)
  · exact Extraction.initial_ratios m (by omega) θ φ
      (fun n hn hnm => (hθ n hn hnm).ne')
      (Extraction.canonical_initial m (by omega) F θ)
  · intro d; exact Extraction.remainder_unit d a F (hF d)
  · intro d
    apply Extraction.remainder_bandwidth d m (by omega) a φ F (hb d)
      (Extraction.quotient_relation d φ (fun n _ => (hφ n).ne'))
      (fun n _ => (hφ n).ne')
    exact Extraction.canonical_recurrence d m (by omega) F θ
      (fun n hn _ => (hext n hn).ne')
  · intro d; exact Extraction.remainder_factorization d a F (hF d)

#print axioms product_compatible
#print axioms sameProduct_iff_entries
#print axioms global_extraction
end BTP.SemiInfinite
