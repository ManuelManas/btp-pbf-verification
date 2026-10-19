import WeightedShift

/-!
# Lower-banded matrices and extraction derivatives

Coordinates of `LowerBand m` are indexed by subdiagonal and column:
`E r j` is the actual matrix entry `(j+r+1,j)`.
-/

open scoped BigOperators
noncomputable section
namespace BTP.GeneralStability

abbrev Seq := BTP.Stability.BoundedSequence
abbrev LowerBand (m : ℕ) := Fin m → Seq
abbrev FactorVariations (p : ℕ) := Fin p → Seq

/-- Actual strictly lower matrix represented by bounded subdiagonals. -/
def bandEntry {m : ℕ} (E : LowerBand m) (i j : ℕ) : ℝ :=
  if h : j < i ∧ i ≤ j+m then E ⟨i-j-1, by omega⟩ j else 0

/-- Actual unit lower matrix represented by its strict subdiagonals. -/
def unitBandEntry {m : ℕ} (E : LowerBand m) (i j : ℕ) : ℝ :=
  if i=j then 1 else bandEntry E i j

/-- A factor variation starts at row `first`; earlier entries are fixed. -/
def initialExtension (first : ℕ) (h : Seq) (n : ℕ) : ℝ :=
  if first ≤ n then h (n-first) else 0

/-- The prescribed finite-dimensional family of initial entries is kept
fixed by extending each factor variation from its first free row. -/
def perturbedFactors {p : ℕ} (a : Fin p → Seq) (h : FactorVariations p)
    (i : Fin p) (n : ℕ) : ℝ :=
  a i n + initialExtension (p-i.val) (h i) n

@[simp] theorem bandEntry_coordinate {m : ℕ} (E : LowerBand m) (r : Fin m) (j : ℕ) :
    bandEntry E (j+r.val+1) j = E r j := by
  simp only [bandEntry]
  split_ifs with h
  · congr 1
    congr 1
    apply Fin.ext
    dsimp
    omega

  · omega

@[simp] theorem bandEntry_upper {m : ℕ} (E : LowerBand m) {i j : ℕ} (h : i ≤ j) :
    bandEntry E i j = 0 := by simp [bandEntry, not_lt.mpr h]

@[simp] theorem bandEntry_outside {m : ℕ} (E : LowerBand m) {i j : ℕ} (h : j+m < i) :
    bandEntry E i j = 0 := by simp [bandEntry, not_le.mpr h]

/-- `G s n` denotes the entry in row n, column n-s. The zeroth
coefficient is the diagonal. Only s≤n represents a matrix entry. -/
abbrev RowCoefficients := ℕ → ℕ → ℝ

/-- The actual semi-infinite lower triangular matrix determined by row
coefficients. Coefficients with s>n are deliberately ignored. -/
def coefficientMatrix (G : RowCoefficients) (i j : ℕ) : ℝ :=
  if j ≤ i then G (i-j) i else 0

/-- Multiplication on the right by the unit bidiagonal with entries b. -/
def rightBidiagonal (G : RowCoefficients) (b : ℕ → ℝ) : RowCoefficients
  | 0, n => G 0 n
  | s+1, n => G (s+1) n + G s n * b (n-s)

/-- Coefficients of an actual ordered product of k unit lower
bidiagonals b₀,…,bₖ₋₁, obtained by right multiplication. -/
def productCoefficients (b : ℕ → ℕ → ℝ) : ℕ → RowCoefficients
  | 0 => fun s _ => if s=0 then 1 else 0
  | k+1 => rightBidiagonal (productCoefficients b k) (b k)

@[simp] theorem productCoefficients_diagonal (b : ℕ → ℕ → ℝ) (k n : ℕ) :
    productCoefficients b k 0 n = 1 := by
  induction k with
  | zero => simp [productCoefficients]
  | succ k ih => exact ih

theorem productCoefficients_band (b : ℕ → ℕ → ℝ) (k s n : ℕ) (h : k < s) :
    productCoefficients b k s n = 0 := by
  induction k generalizing s with
  | zero => simp [productCoefficients, Nat.ne_of_gt h]
  | succ k ih =>
    cases s with
    | zero => omega
    | succ s =>
      change productCoefficients b k (s+1) n + productCoefficients b k s n * b k (n-s) = 0
      rw [ih (s+1) (by omega), ih s (by omega)]
      ring

/-- The matrix identity behind `rightBidiagonal`. It is the two-term
entry formula for multiplication by a unit lower bidiagonal. -/
theorem rightBidiagonal_matrix (G : RowCoefficients) (b : ℕ → ℝ) (i j : ℕ) :
    coefficientMatrix (rightBidiagonal G b) i j =
      coefficientMatrix G i j + coefficientMatrix G i (j+1) * b (j+1) := by
  by_cases hlt : j < i
  · obtain ⟨s, hs⟩ : ∃ s, i=j+s+1 := by exact ⟨i-j-1, by omega⟩
    subst i
    have hji : j ≤ j+s+1 := by omega
    have hj : j+1 ≤ j+s+1 := by omega
    have hsub : j+s+1-j = s+1 := by omega
    have hsub' : j+s+1-(j+1) = s := by omega
    have hlast : j+s+1-s = j+1 := by omega
    simp only [coefficientMatrix, ite_eq_left hji, ite_eq_left hj,
      hsub, hsub', rightBidiagonal, hlast]
  · by_cases he : i=j
    · subst i
      simp [coefficientMatrix, rightBidiagonal]
    · have hji : ¬j ≤ i := by omega
      have hj : ¬j+1 ≤ i := by omega
      simp [coefficientMatrix, hji, hj]

/-- Coefficients of H G, where H has subdiagonal h and zero elsewhere. -/
def leftVariation (h : ℕ → ℝ) (G : RowCoefficients) : RowCoefficients
  | 0, _ => 0
  | s+1, n => h n * G s (n-1)

/-- First-order coefficient equations of H G + L(a) R. -/
def extractionDerivative (a h : ℕ → ℝ) (G R : RowCoefficients) : RowCoefficients
  | 0, n => R 0 n
  | s+1, n => h n * G s (n-1) + R (s+1) n + a n * R s (n-1)

/-- Finite row elimination of the remaining-product variation. -/
def eliminate (a : ℕ → ℝ) (E : RowCoefficients) : RowCoefficients
  | 0, _ => 0
  | s+1, n => E (s+1) n - a n * eliminate a E s (n-1)

/-- The scalar residual after all strictly lower remainder coefficients
have been eliminated. -/
def scalarResidual (a h : ℕ → ℝ) (G : RowCoefficients) (k n : ℕ) : ℝ :=
  eliminate a (leftVariation h G) (k+1) n

/-- Successive first-order operators D₁,…,Dₖ with the exact shifts of the
manuscript, numbered from zero in the family b. -/
def firstOrderProduct (a : ℕ → ℝ) (b : ℕ → ℕ → ℝ) (h : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, n => h n
  | k+1, n => b k (n-(k+1)) * firstOrderProduct a b h k n -
      a n * firstOrderProduct a b h k (n-1)

theorem eliminate_add (a : ℕ → ℝ) (E F : RowCoefficients) (s n : ℕ) :
    eliminate a (fun s n => E s n + F s n) s n =
      eliminate a E s n + eliminate a F s n := by
  induction s generalizing n with
  | zero => simp [eliminate]
  | succ s ih => simp only [eliminate, ih]; ring

theorem eliminate_sub (a : ℕ → ℝ) (E F : RowCoefficients) (s n : ℕ) :
    eliminate a (fun s n => E s n - F s n) s n =
      eliminate a E s n - eliminate a F s n := by
  induction s generalizing n with
  | zero => simp [eliminate]
  | succ s ih => simp only [eliminate, ih]; ring

/-- Elimination recovers R plus the scalar residual, without any infinite
series, existence assumption, or analytic hypothesis. -/
theorem eliminate_extractionDerivative (a h : ℕ → ℝ) (G R : RowCoefficients)
    (hR0 : ∀ n, R 0 n = 0) (s n : ℕ) :
    eliminate a (extractionDerivative a h G R) s n =
      eliminate a (leftVariation h G) s n + R s n := by
  induction s generalizing n with
  | zero => simp [eliminate, hR0]
  | succ s ih =>
    simp only [eliminate, extractionDerivative, leftVariation, ih]
    ring

/-- Right multiplication of G by one bidiagonal adds precisely the two
terms required for the next first-order scalar operator. -/
theorem eliminate_rightBidiagonal (a h b : ℕ → ℝ) (G : RowCoefficients) (s n : ℕ) :
    eliminate a (leftVariation h (rightBidiagonal G b)) (s+1) n =
      eliminate a (leftVariation h G) (s+1) n +
        b (n-s) * eliminate a (leftVariation h G) s n := by
  induction s generalizing n with
  | zero => simp [eliminate, leftVariation, rightBidiagonal]
  | succ s ih =>
    change h n * (G (s+1) (n-1) + G s (n-1)*b ((n-1)-s)) -
      a n * eliminate a (leftVariation h (rightBidiagonal G b)) (s+1) (n-1) = _
    rw [ih]
    have he : (n-1)-s = n-(s+1) := by omega
    simp only [eliminate, leftVariation, he]
    ring

/-- Exact arbitrary-bandwidth factorization of the scalar equation into
first-order operators. This is equation `stab:eq:derivative-product`. -/
theorem scalarResidual_eq_firstOrderProduct (a h : ℕ → ℝ) (b : ℕ → ℕ → ℝ)
    (k n : ℕ) :
    scalarResidual a h (productCoefficients b k) k n = firstOrderProduct a b h k n := by
  induction k generalizing n with
  | zero => simp [scalarResidual, eliminate, leftVariation, productCoefficients, firstOrderProduct]
  | succ k ih =>
    change eliminate a (leftVariation h (rightBidiagonal (productCoefficients b k) (b k)))
      (k+1+1) n = _
    rw [eliminate_rightBidiagonal]
    change (h n * productCoefficients b k (k+1) (n-1) -
      a n * scalarResidual a h (productCoefficients b k) k (n-1)) +
      b k (n-(k+1))*scalarResidual a h (productCoefficients b k) k n = _
    rw [productCoefficients_band b k (k+1) (n-1) (by omega), ih, ih]
    simp only [firstOrderProduct]
    ring

/-- Every solution of the actual coefficient equations satisfies the
factored scalar equation. The hypotheses say that R is strictly lower
and has bandwidth at most k, exactly as in the matrix derivative. -/
theorem extraction_scalar_equation (a h : ℕ → ℝ) (b : ℕ → ℕ → ℝ)
    (R E : RowCoefficients) (k : ℕ) (hR0 : ∀ n, R 0 n = 0)
    (hRtop : ∀ n, R (k+1) n = 0)
    (hE : E = extractionDerivative a h (productCoefficients b k) R) (n : ℕ) :
    firstOrderProduct a b h k n = eliminate a E (k+1) n := by
  subst E
  rw [eliminate_extractionDerivative a h _ R hR0, hRtop, add_zero]
  exact (scalarResidual_eq_firstOrderProduct a h b k n).symm

/-- The actual remaining-product variation obtained by elimination. -/
def remainderCoefficients (a h : ℕ → ℝ) (G E : RowCoefficients) : RowCoefficients :=
  eliminate a (fun s n => E s n - leftVariation h G s n)

@[simp] theorem remainderCoefficients_zero (a h : ℕ → ℝ) (G E : RowCoefficients) (n : ℕ) :
    remainderCoefficients a h G E 0 n = 0 := rfl

/-- Substitution of the reconstructed remainder solves every coefficient
of H G + L(a) R = E. The scalar condition will enforce its top coefficient
being zero, which is precisely the required bandwidth restriction. -/
theorem remainderCoefficients_solves (a h : ℕ → ℝ) (G E : RowCoefficients) (s n : ℕ) :
    extractionDerivative a h G (remainderCoefficients a h G E) (s+1) n = E (s+1) n := by
  simp only [extractionDerivative, remainderCoefficients, eliminate, leftVariation]
  ring

theorem remainderCoefficients_unique (a h : ℕ → ℝ) (G E R : RowCoefficients)
    (hR0 : ∀ n, R 0 n = 0)
    (hE : ∀ s n, extractionDerivative a h G R (s+1) n = E (s+1) n) :
    R = remainderCoefficients a h G E := by
  funext s n
  induction s generalizing n with
  | zero => exact hR0 n
  | succ s ih =>
    have he := hE s n
    simp only [extractionDerivative] at he
    change R (s+1) n = E (s+1) n - h n * G s (n-1) -
      a n * eliminate a (fun s n => E s n-leftVariation h G s n) s (n-1)
    rw [ih] at he
    change h n * G s (n-1) + R (s+1) n + a n *
      eliminate a (fun s n => E s n-leftVariation h G s n) s (n-1) = E (s+1) n at he
    linarith

/-- The arbitrary-bandwidth scalar reduction is an equivalence, not only
a necessary consequence: the constructed remainder has vanishing top
coefficient exactly when the factored scalar equation holds. -/
theorem extraction_scalar_equivalence (a h : ℕ → ℝ) (b : ℕ → ℕ → ℝ)
    (E : RowCoefficients) (k n : ℕ) :
    remainderCoefficients a h (productCoefficients b k) E (k+1) n = 0 ↔
      firstOrderProduct a b h k n = eliminate a E (k+1) n := by
  unfold remainderCoefficients
  rw [eliminate_sub]
  change eliminate a E (k+1) n -
    scalarResidual a h (productCoefficients b k) k n = 0 ↔ _
  rw [scalarResidual_eq_firstOrderProduct]
  constructor <;> intro hh <;> linarith

#print axioms rightBidiagonal_matrix
#print axioms eliminate_extractionDerivative
#print axioms scalarResidual_eq_firstOrderProduct
#print axioms extraction_scalar_equation
#print axioms remainderCoefficients_solves
#print axioms remainderCoefficients_unique
#print axioms extraction_scalar_equivalence

end BTP.GeneralStability
