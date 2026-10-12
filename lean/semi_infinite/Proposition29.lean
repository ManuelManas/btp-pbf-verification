import Lemma24

/-!
# Proposition 2.9: determining successive factors by linear recurrences

Date: 2026-10-08. Version: v01.
Source: BTP_PBF_Normal_2026-10-07_v16.tex, `prop:successive-recurrences`.

Rows are indexed from zero. `G n k` denotes a matrix entry. Only indices
less than `d` occur in the finite matrix. The sum in `rhs` uses `j = 0,…,r-1`,
which is the manuscript's summation index minus one.
-/

open scoped BigOperators Topology Matrix.Norms.Elementwise
open Finset Matrix Filter
noncomputable section

namespace BTP.Extraction

abbrev NatMatrix := ℕ → ℕ → ℝ

def finiteMatrix (d : ℕ) (G : NatMatrix) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of (fun i j => G i j)

def UnitLower (d : ℕ) (G : NatMatrix) : Prop :=
  (∀ n < d, G n n = 1) ∧ ∀ n < d, ∀ k < d, n < k → G n k = 0

def Bandwidth (d r : ℕ) (G : NatMatrix) : Prop :=
  ∀ n < d, ∀ k < d, k + r < n → G n k = 0

def OuterNonzero (d r : ℕ) (G : NatMatrix) : Prop :=
  ∀ n, r ≤ n → n < d → G n (n - r) ≠ 0

def initialValue (r : ℕ) (θ : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∏ h ∈ Ico n (r - 1), θ (h + 1)

def InitialData (r : ℕ) (θ φ : ℕ → ℝ) : Prop :=
  ∀ n < r, φ n = initialValue r θ n

def rhs (r : ℕ) (G : NatMatrix) (φ : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ range r, (-1 : ℝ) ^ j * G (n - (j + 1)) (n - r) * φ (n - (j + 1))

def Recurrence (d r : ℕ) (G : NatMatrix) (φ : ℕ → ℝ) : Prop :=
  ∀ n, r ≤ n → n < d → G n (n - r) * φ n = rhs r G φ n

/-- The order-r recurrence defines the later terms by division by its leading coefficient. -/
def canonicalSequence (r : ℕ) (hr : 0 < r) (G : NatMatrix) (θ : ℕ → ℝ) (n : ℕ) : ℝ :=
  if _h : n < r then initialValue r θ n
  else (∑ j ∈ range r, (-1 : ℝ) ^ j * G (n - (j + 1)) (n - r) *
    canonicalSequence r hr G θ (n - (j + 1))) / G n (n - r)
termination_by n

/-- The prescribed initial data are recovered exactly. -/
theorem canonical_initial (r : ℕ) (hr : 0 < r) (G : NatMatrix) (θ : ℕ → ℝ) :
    InitialData r θ (canonicalSequence r hr G θ) := by
  intro n hn
  rw [canonicalSequence, dite_eq_left hn]

/-- Nonzero extreme entries suffice to continue the sequence. -/
theorem canonical_recurrence (d r : ℕ) (hr : 0 < r) (G : NatMatrix) (θ : ℕ → ℝ)
    (hg : OuterNonzero d r G) : Recurrence d r G (canonicalSequence r hr G θ) := by
  intro n hnr hnd
  rw [canonicalSequence]
  simp only [show ¬n < r by omega, dite_false]
  dsimp [rhs]
  field_simp [hg n hnr hnd]

/-- The initial data and the recurrence determine every term below d uniquely. -/
theorem sequence_unique (d r : ℕ) (hr : 0 < r) (G : NatMatrix) (θ φ ψ : ℕ → ℝ)
    (hg : OuterNonzero d r G) (hφi : InitialData r θ φ) (hψi : InitialData r θ ψ)
    (hφr : Recurrence d r G φ) (hψr : Recurrence d r G ψ) :
    ∀ n < d, φ n = ψ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hnd
    by_cases hn : n < r
    · rw [hφi n hn, hψi n hn]
    · apply mul_left_cancel₀ (hg n (by omega) hnd)
      rw [hφr n (by omega) hnd, hψr n (by omega) hnd]
      apply Finset.sum_congr rfl
      intro j hj
      rw [ih (n - (j + 1)) (by omega) (by omega)]

/-- The entry of the remaining matrix at row k+t, column k, computed recursively. -/
def columnRemainder (a : ℕ → ℝ) (G : NatMatrix) (k : ℕ) : ℕ → ℝ
  | 0 => G k k
  | t + 1 => G (k + (t + 1)) k - a (k + (t + 1)) * columnRemainder a G k t

def remainder (a : ℕ → ℝ) (G : NatMatrix) (n k : ℕ) : ℝ :=
  if k ≤ n then columnRemainder a G k (n - k) else 0

def RatioRelation (d : ℕ) (a φ : ℕ → ℝ) : Prop :=
  ∀ n, 0 < n → n < d → a n * φ n = φ (n - 1)

/-- Multiplying by φ telescopes the products of successive bidiagonal entries. -/
theorem weighted_remainder (d : ℕ) (a φ : ℕ → ℝ) (G : NatMatrix)
    (hrel : RatioRelation d a φ) (k t : ℕ) (hkt : k + t < d) :
    φ (k + t) * columnRemainder a G k t =
      ∑ j ∈ range (t + 1), (-1 : ℝ) ^ j * G (k + t - j) k * φ (k + t - j) := by
  induction t with
  | zero => simp [columnRemainder, mul_comm]
  | succ t ih =>
    have hp := hrel (k + (t + 1)) (by omega) hkt
    have hn : k + (t + 1) - 1 = k + t := by omega
    rw [hn] at hp
    rw [columnRemainder, mul_sub, ← mul_assoc, mul_comm (φ _) (a _), hp]
    rw [ih (by omega)]
    conv_rhs => rw [Finset.sum_range_succ']
    simp only [pow_zero, one_mul, Nat.sub_zero]
    have hsum : (∑ j ∈ range (t + 1), (-1 : ℝ) ^ (j + 1) *
        G (k + (t + 1) - (j + 1)) k * φ (k + (t + 1) - (j + 1))) =
        -(∑ j ∈ range (t + 1), (-1 : ℝ) ^ j * G (k + t - j) k * φ (k + t - j)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      have he : k + (t + 1) - (j + 1) = k + t - j := by omega
      rw [he, pow_succ]
      ring
    rw [hsum]
    ring

/-- The row-r boundary entry vanishes exactly when the recurrence holds. -/
theorem boundary_identity (d r : ℕ) (a φ : ℕ → ℝ) (G : NatMatrix)
    (hrel : RatioRelation d a φ) (n : ℕ) (hrn : r ≤ n) (hnd : n < d) :
    φ n * columnRemainder a G (n - r) r = G n (n - r) * φ n - rhs r G φ n := by
  have h := weighted_remainder d a φ G hrel (n - r) r (by omega)
  have he : n - r + r = n := by omega
  rw [he, Finset.sum_range_succ'] at h
  simp only [pow_zero, one_mul, Nat.sub_zero] at h
  rw [h]
  dsimp [rhs]
  have hs : (∑ j ∈ range r, (-1 : ℝ) ^ (j + 1) * G (n - (j + 1)) (n - r) * φ (n - (j + 1))) =
      -(∑ j ∈ range r, (-1 : ℝ) ^ j * G (n - (j + 1)) (n - r) * φ (n - (j + 1))) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [pow_succ]
    ring
  rw [hs]
  ring

/-- The recursively computed remainder is still unit lower triangular. -/
theorem remainder_unit (d : ℕ) (a : ℕ → ℝ) (G : NatMatrix) (hG : UnitLower d G) :
    UnitLower d (remainder a G) := by
  constructor
  · intro n hn
    simpa [remainder, columnRemainder] using hG.1 n hn
  · intro n hn k hk hnk
    simp [remainder, show ¬ k ≤ n by omega]

/-- The recursive remainder solves the actual finite matrix equation. -/
theorem remainder_factorization (d : ℕ) (a : ℕ → ℝ) (G : NatMatrix) (hG : UnitLower d G) :
    bidiagonal d a * finiteMatrix d (remainder a G) = finiteMatrix d G := by
  ext i j
  by_cases hi : 0 < i.val
  · rw [bidiagonal_mul_pos _ _ _ _ hi]
    simp only [finiteMatrix, Matrix.of_apply]
    by_cases hji : j.val < i.val
    · have hj : j.val ≤ i.val := by omega
      have hjprev : j.val ≤ i.val - 1 := by omega
      have he : i.val - j.val = (i.val - 1 - j.val) + 1 := by omega
      have he' : j.val + (i.val - 1 - j.val + 1) = i.val := by omega
      simp only [remainder, hj, hjprev, ite_true, he, columnRemainder, he']
      ring
    · by_cases heq : j.val = i.val
      · have hjprev : ¬ i.val ≤ i.val - 1 := by omega
        simp [remainder, heq, hjprev, columnRemainder]
      · have hj : ¬ j.val ≤ i.val := by omega
        have hjprev : ¬ j.val ≤ i.val - 1 := by omega
        simp only [remainder, hj, hjprev, ite_false, mul_zero, add_zero]
        exact (hG.2 i i.isLt j j.isLt (by omega)).symm
  · have hi0 : i.val = 0 := by omega
    rw [bidiagonal_mul_zero _ _ _ _ hi0]
    simp only [finiteMatrix, Matrix.of_apply]
    by_cases hj : j.val = 0
    · simp [remainder, hi0, hj, columnRemainder]
    · simp only [remainder, show ¬j.val ≤ i.val by omega, ite_false]
      exact (hG.2 i i.isLt j j.isLt (by omega)).symm

/-- Unit lower bidiagonal matrices have determinant one, regardless of signs. -/
theorem bidiagonal_det (d : ℕ) (a : ℕ → ℝ) : (bidiagonal d a).det = 1 := by
  have hl : (bidiagonal d a).IsLowerTriangular := by
    intro i j hij
    have h : i.val < j.val := hij
    exact (bidiagonal_unit d a).2 i j (by intro heq; subst j; omega) (by omega)
  rw [Matrix.det_of_isLowerTriangular _ hl]
  simp [(bidiagonal_unit d a).1]

/-- In particular, the remainder really is L(a)^{-1}G. -/
theorem remainder_inverse (d : ℕ) (a : ℕ → ℝ) (G : NatMatrix) (hG : UnitLower d G) :
    finiteMatrix d (remainder a G) = (bidiagonal d a)⁻¹ * finiteMatrix d G := by
  rw [← remainder_factorization d a G hG, ← Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ (by rw [bidiagonal_det]; exact isUnit_one), Matrix.one_mul]

/-- The recurrence kills the r-th subdiagonal; the row recursion then kills
all entries farther below it. -/
theorem remainder_bandwidth (d r : ℕ) (hr : 0 < r) (a φ : ℕ → ℝ) (G : NatMatrix)
    (hb : Bandwidth d r G) (hrel : RatioRelation d a φ) (hφ : ∀ n < d, φ n ≠ 0)
    (hrec : Recurrence d r G φ) : Bandwidth d (r - 1) (remainder a G) := by
  have hboundary : ∀ k, k + r < d → columnRemainder a G k r = 0 := by
    intro k hk
    have hid := boundary_identity d r a φ G hrel (k + r) (by omega) hk
    rw [hrec (k + r) (by omega) hk, sub_self] at hid
    have he : k + r - r = k := by omega
    rw [he] at hid
    exact (mul_eq_zero.mp hid).resolve_left (hφ (k + r) hk)
  have htail : ∀ k t, r ≤ t → k + t < d → columnRemainder a G k t = 0 := by
    intro k t ht
    induction t, ht using Nat.le_induction with
    | base => exact hboundary k
    | succ t ht ih =>
      intro hkt
      rw [columnRemainder, ih (by omega), mul_zero, sub_zero]
      exact hb (k + (t + 1)) hkt k (by omega) (by omega)
  intro n hn k hk hkn
  have hle : k ≤ n := by omega
  rw [remainder, ite_eq_left hle]
  exact htail k (n - k) (by omega) (by omega)

/-- Quotients of nonzero successive terms satisfy the telescoping relation. -/
theorem quotient_relation (d : ℕ) (φ : ℕ → ℝ) (hφ : ∀ n < d, φ n ≠ 0) :
    RatioRelation d (fun n => φ (n - 1) / φ n) φ := by
  intro n hn hnd
  exact div_mul_cancel₀ _ (hφ n hnd)

/-- Prefix products of the subdiagonal entries. -/
def prefixProduct (a : ℕ → ℝ) (n : ℕ) : ℝ := ∏ h ∈ range n, a (h + 1)

@[simp] theorem prefix_zero (a : ℕ → ℝ) : prefixProduct a 0 = 1 := by simp [prefixProduct]

theorem prefix_succ (a : ℕ → ℝ) (n : ℕ) : prefixProduct a (n + 1) = prefixProduct a n * a (n + 1) := by
  exact Finset.prod_range_succ _ _

theorem prefix_nonzero (d : ℕ) (a : ℕ → ℝ)
    (ha : ∀ n, 0 < n → n < d → a n ≠ 0) (n : ℕ) (hn : n < d) : prefixProduct a n ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro h hh
  exact ha (h + 1) (by omega) (by have := mem_range.mp hh; omega)

/-- The unique normalization with φ_{r-1}=1 for a given nonzero factor. -/
def normalizedPhi (r : ℕ) (a : ℕ → ℝ) (n : ℕ) : ℝ := prefixProduct a (r - 1) / prefixProduct a n

theorem normalized_nonzero (d r : ℕ) (hr : 0 < r) (hrd : r ≤ d) (a : ℕ → ℝ)
    (ha : ∀ n, 0 < n → n < d → a n ≠ 0) :
    ∀ n < d, normalizedPhi r a n ≠ 0 := by
  intro n hn
  exact div_ne_zero (prefix_nonzero d a ha (r - 1) (by omega)) (prefix_nonzero d a ha n hn)

theorem normalized_relation (d r : ℕ) (a : ℕ → ℝ)
    (ha : ∀ n, 0 < n → n < d → a n ≠ 0) : RatioRelation d a (normalizedPhi r a) := by
  intro n hn hnd
  have hprev : prefixProduct a (n - 1) ≠ 0 := prefix_nonzero d a ha (n - 1) (by omega)
  have hn' : n = (n - 1) + 1 := by omega
  have hpref : prefixProduct a n = prefixProduct a (n - 1) * a n := by
    conv_lhs => rw [hn', prefix_succ]
    rw [← hn']
  dsimp [normalizedPhi]
  rw [hpref]
  field_simp [hprev, ha n hn hnd]

/-- Prefix cancellation gives exactly the initial products in the manuscript. -/
theorem normalized_initial (d r : ℕ) (hr : 0 < r) (hrd : r ≤ d) (a : ℕ → ℝ)
    (ha : ∀ n, 0 < n → n < d → a n ≠ 0) : InitialData r a (normalizedPhi r a) := by
  intro n hn
  apply (div_eq_iff (prefix_nonzero d a ha n (by omega))).mpr
  have h := (Finset.prod_range_mul_prod_Ico (fun h => a (h + 1)) (by omega : n ≤ r - 1)).symm
  simpa [prefixProduct, initialValue, mul_comm] using h

/-- Consecutive initial ratios are the freely chosen θ entries. -/
theorem initial_ratios (r : ℕ) (hr : 0 < r) (θ φ : ℕ → ℝ)
    (hθ : ∀ n, 0 < n → n < r → θ n ≠ 0) (hinit : InitialData r θ φ) :
    ∀ n, 0 < n → n < r → φ (n - 1) / φ n = θ n := by
  intro n hn hnr
  have hnz := normalized_nonzero r r hr le_rfl θ hθ n hnr
  have hi := normalized_initial r r hr le_rfl θ hθ
  have he : φ (n - 1) = normalizedPhi r θ (n - 1) := by
    rw [hinit (n - 1) (by omega), hi (n - 1) (by omega)]
  have he' : φ n = normalizedPhi r θ n := (hinit n hnr).trans (hi n hnr).symm
  rw [he, he']
  apply (div_eq_iff hnz).mpr
  exact (normalized_relation r r θ hθ n hn hnr).symm

theorem initial_normalization (r : ℕ) (hr : 0 < r) (θ φ : ℕ → ℝ)
    (hinit : InitialData r θ φ) : φ (r - 1) = 1 := by
  rw [hinit (r - 1) (by omega)]
  simp [initialValue]

/-- If L(a)H=G, the computed remainder agrees with H; no sign assumption is needed. -/
theorem remainder_of_factorization (d : ℕ) (a : ℕ → ℝ) (G : NatMatrix)
    (hG : UnitLower d G) (H : Matrix (Fin d) (Fin d) ℝ)
    (hfact : bidiagonal d a * H = finiteMatrix d G) :
    finiteMatrix d (remainder a G) = H := by
  rw [remainder_inverse d a G hG, ← hfact, ← Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ (by rw [bidiagonal_det]; exact isUnit_one), Matrix.one_mul]

/-- Conversely, removing a factor and reducing the bandwidth forces the recurrence. -/
theorem recurrence_of_factorization (d r : ℕ) (hr : 0 < r) (a φ : ℕ → ℝ) (G H : NatMatrix)
    (hG : UnitLower d G) (hrel : RatioRelation d a φ) (hband : Bandwidth d (r - 1) H)
    (hfact : bidiagonal d a * finiteMatrix d H = finiteMatrix d G) : Recurrence d r G φ := by
  have heq := remainder_of_factorization d a G hG (finiteMatrix d H) hfact
  intro n hnr hnd
  have hnk : n - r < d := by omega
  have hentry := congrArg (fun M : Matrix (Fin d) (Fin d) ℝ => M ⟨n, hnd⟩ ⟨n - r, hnk⟩) heq
  have hzero : columnRemainder a G (n - r) r = 0 := by
    have he : n - (n - r) = r := by omega
    simpa [finiteMatrix, remainder, he,
      hband n hnd (n - r) hnk (by omega)] using hentry
  have hid := boundary_identity d r a φ G hrel n hnr hnd
  rw [hzero, mul_zero] at hid
  linarith

/-- Forward half of Proposition 2.9, including the initial entries,
the actual matrix inverse and the reduced bandwidth. -/
theorem proposition_2_9_forward (d r : ℕ) (hr : 2 ≤ r) (_hrd : r < d)
    (G : NatMatrix) (θ : ℕ → ℝ) (hG : UnitLower d G) (hb : Bandwidth d r G)
    (hg : OuterNonzero d r G) (hθ : ∀ n, 0 < n → n < r → θ n ≠ 0)
    (hφ : ∀ n < d, canonicalSequence r (by omega) G θ n ≠ 0) :
    let φ := canonicalSequence r (by omega) G θ
    let a := fun n => φ (n - 1) / φ n
    InitialData r θ φ ∧ Recurrence d r G φ ∧ φ (r - 1) = 1 ∧
    (∀ n, 0 < n → n < r → a n = θ n) ∧
    (∀ n, 0 < n → n < d → a n ≠ 0) ∧
    UnitLower d (remainder a G) ∧ Bandwidth d (r - 1) (remainder a G) ∧
    bidiagonal d a * finiteMatrix d (remainder a G) = finiteMatrix d G ∧
    finiteMatrix d (remainder a G) = (bidiagonal d a)⁻¹ * finiteMatrix d G := by
  dsimp only
  have hi := canonical_initial r (by omega) G θ
  have hc := canonical_recurrence d r (by omega) G θ hg
  refine ⟨hi, hc, initial_normalization r (by omega) θ _ hi,
    initial_ratios r (by omega) θ _ hθ hi, ?_, remainder_unit d _ G hG,
    remainder_bandwidth d r (by omega) _ _ G hb (quotient_relation d _ hφ) hφ hc,
    remainder_factorization d _ G hG, remainder_inverse d _ G hG⟩
  intro n hn hnd
  exact div_ne_zero (hφ (n - 1) (by omega)) (hφ n hnd)

/-- Converse half: every admissible extracted factor is recovered by the unique
normalized solution of the prescribed recurrence, with θ_h=a_h. -/
theorem proposition_2_9_converse (d r : ℕ) (hr : 2 ≤ r) (hrd : r < d)
    (G H : NatMatrix) (a : ℕ → ℝ) (hG : UnitLower d G)
    (hg : OuterNonzero d r G) (ha : ∀ n, 0 < n → n < d → a n ≠ 0)
    (hb : Bandwidth d (r - 1) H)
    (hfact : bidiagonal d a * finiteMatrix d H = finiteMatrix d G) :
    let φ := canonicalSequence r (by omega) G a
    (∀ n < d, φ n = normalizedPhi r a n) ∧ (∀ n < d, φ n ≠ 0) ∧
    φ (r - 1) = 1 ∧
    (∀ n, 0 < n → n < d → a n = φ (n - 1) / φ n) ∧
    InitialData r a φ ∧ Recurrence d r G φ := by
  dsimp only
  have hn := normalized_nonzero d r (by omega) (by omega) a ha
  have hi := normalized_initial d r (by omega) (by omega) a ha
  have hrel := normalized_relation d r a ha
  have hrec := recurrence_of_factorization d r (by omega) a (normalizedPhi r a) G H hG hrel hb hfact
  have heq := sequence_unique d r (by omega) G a _ _ hg
    (canonical_initial r (by omega) G a) hi (canonical_recurrence d r (by omega) G a hg) hrec
  refine ⟨heq, ?_, initial_normalization r (by omega) a _ (canonical_initial r (by omega) G a),
    ?_, canonical_initial r (by omega) G a, canonical_recurrence d r (by omega) G a hg⟩
  · intro n hnd
    rw [heq n hnd]
    exact hn n hnd
  · intro n hn' hnd
    rw [heq n hnd, heq (n - 1) (by omega)]
    symm
    exact (div_eq_iff (hn n hnd)).mpr (hrel n hn' hnd).symm

/-- Only θ_1,…,θ_{r-1} matter, despite representing θ by a total function. -/
theorem initial_parameters_ext (r : ℕ) (θ η : ℕ → ℝ)
    (h : ∀ n, 0 < n → n < r → θ n = η n) (n : ℕ) :
    initialValue r θ n = initialValue r η n := by
  apply Finset.prod_congr rfl
  intro j hj
  exact h (j + 1) (by omega) (by have := mem_Ico.mp hj; omega)

theorem canonical_parameters_ext (d r : ℕ) (hr : 0 < r) (G : NatMatrix) (θ η : ℕ → ℝ)
    (hg : OuterNonzero d r G) (h : ∀ n, 0 < n → n < r → θ n = η n) :
    ∀ n < d, canonicalSequence r hr G θ n = canonicalSequence r hr G η n := by
  apply sequence_unique d r hr G θ _ _ hg (canonical_initial r hr G θ) ?_
    (canonical_recurrence d r hr G θ hg) (canonical_recurrence d r hr G η hg)
  intro n hn
  rw [canonical_initial r hr G η n hn]
  exact (initial_parameters_ext r θ η h n).symm

/-- Combined characterization: an initial parameter choice admits an extracted
nonzero factor exactly when the canonical recurrence has no zero term. -/
theorem proposition_2_9 (d r : ℕ) (hr : 2 ≤ r) (hrd : r < d)
    (G : NatMatrix) (θ : ℕ → ℝ) (hG : UnitLower d G) (hb : Bandwidth d r G)
    (hg : OuterNonzero d r G) (hθ : ∀ n, 0 < n → n < r → θ n ≠ 0) :
    (∀ n < d, canonicalSequence r (by omega) G θ n ≠ 0) ↔
    ∃ a : ℕ → ℝ,
      (∀ n, 0 < n → n < d → a n ≠ 0) ∧
      (∀ n, 0 < n → n < r → a n = θ n) ∧
      UnitLower d (remainder a G) ∧ Bandwidth d (r - 1) (remainder a G) ∧
      bidiagonal d a * finiteMatrix d (remainder a G) = finiteMatrix d G ∧
      finiteMatrix d (remainder a G) = (bidiagonal d a)⁻¹ * finiteMatrix d G := by
  constructor
  · intro hφ
    obtain ⟨hi, hc, hn, hθ', ha, hunit, hband, hprod, hinv⟩ :=
      proposition_2_9_forward d r hr hrd G θ hG hb hg hθ hφ
    exact ⟨_, ha, hθ', hunit, hband, hprod, hinv⟩
  · rintro ⟨a, ha, hθ', hu, hband, hprod, hinv⟩
    have hc := proposition_2_9_converse d r hr hrd G (remainder a G) a hG hg ha hband hprod
    have he := canonical_parameters_ext d r (by omega) G θ a hg (fun n hn hnr => (hθ' n hn hnr).symm)
    intro n hn
    rw [he n hn]
    exact hc.2.1 n hn

/-- Infinite entry notation for a finite product; its d×d restriction is the
actual product defined in Lemma 2.4. -/
def productEntries (a : Entries) (r : ℕ) (n k : ℕ) : ℝ :=
  if k ≤ n then entry a r n (n - k) else 0

theorem product_finite (d : ℕ) (a : Entries) (r : ℕ) :
    finiteMatrix d (productEntries a r) = lowerProduct d a r := by
  ext i j
  exact (lowerProduct_entry a r i j).symm

theorem product_unit (d : ℕ) (a : Entries) (r : ℕ) : UnitLower d (productEntries a r) := by
  constructor
  · intro n hn
    simp [productEntries]
  · intro n hn k hk hnk
    simp [productEntries, show ¬ k ≤ n by omega]

theorem product_band (d : ℕ) (a : Entries) (r : ℕ) : Bandwidth d r (productEntries a r) := by
  intro n hn k hk hkn
  rw [productEntries, ite_eq_left (by omega : k ≤ n)]
  exact entry_band a r n (n - k) (by omega)

theorem product_outer_positive (d r : ℕ) (a : Entries)
    (ha : ∀ j < r, ∀ n, 0 < n → n < d → 0 < a j n) :
    ∀ n, r ≤ n → n < d → 0 < productEntries a r n (n - r) := by
  intro n hnr hnd
  have he : n - (n - r) = r := by omega
  simp only [productEntries, Nat.sub_le, ite_true, he]
  apply entry_diag_pos a r n hnr
  intro j hj m hm hjm
  exact ha j hj m (by omega) (by omega)

theorem product_extraction (d r : ℕ) (hr : 0 < r) (a : Entries) :
    bidiagonal d (a (r - 1)) * finiteMatrix d (productEntries a (r - 1)) =
      finiteMatrix d (productEntries a r) := by
  rw [product_finite, product_finite]
  have he : r = r - 1 + 1 := by omega
  conv_rhs => rw [he, lowerProduct]

/-- All p-1 stages of a positive factorization, with orders p,p-1,…,2.
Each stage uses the remaining product, and its outer diagonal is positive. -/
theorem positive_iteration (d p : ℕ) (hpd : p < d) (a : Entries)
    (ha : ∀ j < p, ∀ n, 0 < n → n < d → 0 < a j n) :
    ∀ (r : ℕ) (hr : 2 ≤ r) (_hrp : r ≤ p),
      let G := productEntries a r
      let φ := canonicalSequence r (by omega) G (a (r - 1))
      UnitLower d G ∧ Bandwidth d r G ∧ OuterNonzero d r G ∧
      (∀ n < d, φ n ≠ 0) ∧ φ (r - 1) = 1 ∧
      InitialData r (a (r - 1)) φ ∧ Recurrence d r G φ ∧
      (∀ n, 0 < n → n < d → a (r - 1) n = φ (n - 1) / φ n) ∧
      finiteMatrix d (remainder (a (r - 1)) G) = lowerProduct d a (r - 1) := by
  intro r hr hrp
  dsimp only
  have hunit := product_unit d a r
  have hband := product_band d a r
  have houter : OuterNonzero d r (productEntries a r) := by
    intro n hnr hnd
    exact ne_of_gt (product_outer_positive d r a
      (fun j hj n hn hnd => ha j (by omega) n hn hnd) n hnr hnd)
  have hfactor : ∀ n, 0 < n → n < d → a (r - 1) n ≠ 0 := by
    intro n hn hnd
    exact ne_of_gt (ha (r - 1) (by omega) n hn hnd)
  have hprod := product_extraction d r (by omega) a
  obtain ⟨heq, hnz, hnorm, hratio, hi, hc⟩ := proposition_2_9_converse d r hr (by omega)
    (productEntries a r) (productEntries a (r - 1)) (a (r - 1)) hunit houter
    hfactor (product_band d a (r - 1)) hprod
  refine ⟨hunit, hband, houter, hnz, hnorm, hi, hc, hratio, ?_⟩
  exact (remainder_of_factorization d (a (r - 1)) _ hunit _ hprod).trans (product_finite d a (r - 1))

/-- At bandwidth one the remaining product is precisely the final factor. -/
theorem final_factor (d : ℕ) (a : Entries) : lowerProduct d a 1 = bidiagonal d (a 0) := by
  simp [lowerProduct]

/-- The number of recurrence stages is p-1. -/
theorem number_of_recurrences (p : ℕ) : (Icc 2 p).card = p - 1 := by
  simp only [Nat.card_Icc]
  omega

/-- Summing r-1 free initial entries over r=2,…,p gives p(p-1)/2. -/
theorem total_initial_parameters (p : ℕ) (hp : 1 ≤ p) :
    (∑ r ∈ Icc 2 p, (r - 1)) = p * (p - 1) / 2 := by
  have he : (∑ r ∈ Icc 2 p, (r - 1)) = ∑ j ∈ Ico 1 p, j := by
    apply Finset.sum_bij (fun r _ => r - 1)
    · intro r hr
      simp only [mem_Icc] at hr
      simp only [mem_Ico]
      omega
    · intro r hr s hs hrs
      simp only [mem_Icc] at hr hs
      omega
    · intro j hj
      simp only [mem_Ico] at hj
      refine ⟨j + 1, by simp only [mem_Icc]; omega, by omega⟩
    · intro r hr
      rfl
  rw [he]
  have hs := Finset.sum_range_add_sum_Ico (fun j : ℕ => j) hp
  simpa [Finset.sum_range_id] using hs

#print axioms proposition_2_9
#print axioms proposition_2_9_forward
#print axioms proposition_2_9_converse
#print axioms sequence_unique
#print axioms positive_iteration
#print axioms final_factor
#print axioms number_of_recurrences
#print axioms total_initial_parameters

end BTP.Extraction
