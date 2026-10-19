import ExtractionDerivative
import BandLDU

/-! Banach coordinates for matrices of fixed lower and upper bandwidth.
The two triangular sides use the same column-indexed convention as
`LowerBand`; the upper side is represented by its transpose. -/
noncomputable section
open scoped BigOperators
namespace BTP.GeneralStability

abbrev FullBand (p q : ℕ) := LowerBand p × (Seq × LowerBand q)

def fullEntry {p q : ℕ} (E : FullBand p q) (i j : ℕ) : ℝ :=
  if i=j then E.2.1 i else if j < i then bandEntry E.1 i j else bandEntry E.2.2 j i

def fullSection {p q : ℕ} (E : FullBand p q) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => fullEntry E i.val j.val

@[simp] theorem fullEntry_diag {p q : ℕ} (E : FullBand p q) (n : ℕ) :
    fullEntry E n n = E.2.1 n := by simp [fullEntry]

@[simp] theorem fullEntry_lower {p q : ℕ} (E : FullBand p q) (r : Fin p) (n : ℕ) :
    fullEntry E (n+r.val+1) n = E.1 r n := by
  simp [fullEntry, show n+r.val+1 ≠ n by omega, show n<n+r.val+1 by omega]

@[simp] theorem fullEntry_upper {p q : ℕ} (E : FullBand p q) (r : Fin q) (n : ℕ) :
    fullEntry E n (n+r.val+1) = E.2.2 r n := by
  simp [fullEntry, show n ≠ n+r.val+1 by omega, show ¬n+r.val+1 < n by omega]

theorem bandEntry_abs_le {m : ℕ} (E : LowerBand m) (i j : ℕ) :
    |bandEntry E i j| ≤ ‖E‖ := by
  unfold bandEntry
  split_ifs with h
  · exact (BTP.Stability.boundedSequence_abs_le _ _).trans (norm_le_pi_norm E _)
  · simp

theorem fullEntry_abs_le {p q : ℕ} (E : FullBand p q) (i j : ℕ) :
    |fullEntry E i j| ≤ ‖E‖ := by
  unfold fullEntry
  split_ifs
  · exact (BTP.Stability.boundedSequence_abs_le _ _).trans
      ((le_max_left _ _).trans (le_max_right _ _))
  · exact (bandEntry_abs_le _ _ _).trans (le_max_left _ _)
  · exact (bandEntry_abs_le _ _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _))

theorem fullEntry_add {p q : ℕ} (E F : FullBand p q) (i j : ℕ) :
    fullEntry (E+F) i j = fullEntry E i j + fullEntry F i j := by
  simp only [fullEntry, bandEntry]
  split_ifs <;> first | rfl | simp

theorem fullEntry_smul {p q : ℕ} (c : ℝ) (E : FullBand p q) (i j : ℕ) :
    fullEntry (c • E) i j = c * fullEntry E i j := by
  simp only [fullEntry, bandEntry]
  split_ifs <;> simp [smul_eq_mul]

theorem fullEntry_ext {p q : ℕ} {E F : FullBand p q}
    (h : ∀ i j, fullEntry E i j = fullEntry F i j) : E=F := by
  apply Prod.ext
  · funext r
    apply BoundedContinuousFunction.ext
    intro n
    simpa using h (n+r.val+1) n
  · apply Prod.ext
    · apply BoundedContinuousFunction.ext
      intro n
      simpa using h n n
    · funext r
      apply BoundedContinuousFunction.ext
      intro n
      simpa using h n (n+r.val+1)

theorem fullEntry_band {p q : ℕ} (E : FullBand p q) (i j : ℕ)
    (h : j+p < i ∨ i+q < j) : fullEntry E i j=0 := by
  unfold fullEntry
  split_ifs with hij hji
  · subst j; omega
  · apply bandEntry_outside
    omega
  · apply bandEntry_outside
    omega

theorem fullSection_lower_band {p q N : ℕ} (E : FullBand p q) :
    BTP.Stability.BandLDU.LowerBandwidth p (fullSection E N) := by
  intro i j h
  exact fullEntry_band E i j (Or.inl h)

theorem fullSection_upper_band {p q N : ℕ} (E : FullBand p q) :
    BTP.Stability.BandLDU.UpperBandwidth q (fullSection E N) := by
  intro i j h
  exact fullEntry_band E i j (Or.inr h)

/-- Recover band coordinates from actual entries with a uniform bound. -/
def fullOfEntries {p q : ℕ} (f : ℕ → ℕ → ℝ) (C : ℝ)
    (hf : ∀ i j, |f i j| ≤ C) : FullBand p q :=
  (fun r => BTP.Stability.ofAbsBound (fun n => f (n+r.val+1) n) C
    (fun n => hf (n+r.val+1) n),
    BTP.Stability.ofAbsBound (fun n => f n n) C (fun n => hf n n),
    fun r => BTP.Stability.ofAbsBound (fun n => f n (n+r.val+1)) C
      (fun n => hf n (n+r.val+1)))

theorem fullOfEntries_entry {p q : ℕ} (f : ℕ → ℕ → ℝ) (C : ℝ)
    (hf : ∀ i j, |f i j| ≤ C)
    (hband : ∀ i j, j+p < i ∨ i+q < j → f i j=0) (i j : ℕ) :
    fullEntry (fullOfEntries (p:=p) (q:=q) f C hf) i j = f i j := by
  simp only [fullEntry, fullOfEntries, bandEntry, BTP.Stability.ofAbsBound_apply]
  split_ifs <;> try { congr 1 <;> omega }
  all_goals symm; apply hband; omega

theorem norm_fullOfEntries_le {p q : ℕ} (f : ℕ → ℕ → ℝ) (C : ℝ)
    (hf : ∀ i j, |f i j| ≤ C) : ‖fullOfEntries (p:=p) (q:=q) f C hf‖ ≤ C := by
  have hC : 0≤C := (abs_nonneg _).trans (hf 0 0)
  apply max_le
  · apply (pi_norm_le_iff_of_nonneg hC).mpr
    intro r
    apply BoundedContinuousFunction.norm_le_of_nonempty.mpr
    exact fun n => hf _ _
  · apply max_le
    · apply BoundedContinuousFunction.norm_le_of_nonempty.mpr
      exact fun n => hf _ _
    · apply (pi_norm_le_iff_of_nonneg hC).mpr
      intro r
      apply BoundedContinuousFunction.norm_le_of_nonempty.mpr
      exact fun n => hf _ _

end BTP.GeneralStability
