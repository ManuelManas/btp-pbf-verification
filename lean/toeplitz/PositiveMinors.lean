import ToeplitzSymbol

/-! Positivity of all finite minors of an ordered bidiagonal product.
The proof expands the determinant by rows. Repeated rows vanish; every
remaining term has increasing indices and positive or nonnegative weight. -/

open Matrix Finset
noncomputable section
namespace BTP.Toeplitz

def TN (M : Matrix ℕ ℕ ℝ) : Prop :=
  ∀ {k : ℕ} (I J : Fin k → ℕ), StrictMono I → StrictMono J → 0 ≤ (M.submatrix I J).det

def Admissible {k : ℕ} (p q : ℕ) (I J : Fin k → ℕ) : Prop :=
  ∀ i, I i ≤ J i + p ∧ J i ≤ I i + q

/-- TN together with strict positivity of all band-admissible minors. -/
def BandedTP (p q : ℕ) (M : Matrix ℕ ℕ ℝ) : Prop :=
  TN M ∧ ∀ {k : ℕ} (I J : Fin k → ℕ), StrictMono I → StrictMono J →
    Admissible p q I J → 0 < (M.submatrix I J).det

theorem TN.monotone_rows {M : Matrix ℕ ℕ ℝ} (hM : TN M) {k : ℕ}
    (I J : Fin k → ℕ) (hI : Monotone I) (hJ : StrictMono J) :
    0 ≤ (M.submatrix I J).det := by
  by_cases hinj : Function.Injective I
  · exact hM I J (hI.strictMono_of_injective hinj) hJ
  · obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hinj
    rw [Matrix.det_zero_of_row_eq hne (by funext c; exact congrArg (fun t => M t (J c)) hij)]

theorem identity_minor {k : ℕ} (I J : Fin k → ℕ) (hI : StrictMono I) (hJ : StrictMono J) :
    ((1 : Matrix ℕ ℕ ℝ).submatrix I J).det = if I = J then 1 else 0 := by
  by_cases he : I = J
  · subst J
    have hm : (1 : Matrix ℕ ℕ ℝ).submatrix I I = 1 := by
      ext i j
      simp [Matrix.one_apply, hI.injective.eq_iff]
    simp [hm]
  · have hex : ∃ i, ∀ j, I i ≠ J j := by
      by_contra h
      push Not at h
      choose f hf using h
      have hfm : StrictMono f := by
        intro i j hij
        apply hJ.lt_iff_lt.mp
        rw [← hf i, ← hf j]
        exact hI hij
      have hid : f = id := hfm.eq_id
      apply he
      funext i
      simpa only [hid, id_eq] using hf i
    obtain ⟨i, hi⟩ := hex
    rw [Matrix.det_eq_zero_of_row_eq_zero i (by intro j; simp [hi j])]
    simp [he]

theorem identity_BTP : BandedTP 0 0 (1 : Matrix ℕ ℕ ℝ) := by
  constructor
  · intro k I J hI hJ
    rw [identity_minor I J hI hJ]
    split_ifs <;> norm_num
  · intro k I J hI hJ ha
    have he : I = J := by funext i; exact le_antisymm (by simpa using (ha i).1) (by simpa using (ha i).2)
    rw [identity_minor I J hI hJ, ite_eq_left he]
    norm_num

theorem binary_row_expansion {k : ℕ} (M : Matrix ℕ ℕ ℝ) (J : Fin k → ℕ)
    (C : Fin k → Bool → ℝ) (F : Fin k → Bool → ℕ) :
    (Matrix.of fun i j => ∑ b : Bool, C i b * M (F i b) (J j)).det =
      ∑ f : Fin k → Bool, (∏ i, C i (f i)) *
        (M.submatrix (fun i => F i (f i)) J).det := by
  let A : MultilinearMap ℝ (fun _ : Fin k => Fin k → ℝ) ℝ :=
    Matrix.detRowAlternating.toMultilinearMap
  let g := fun i : Fin k => fun b : Bool => fun j : Fin k => C i b * M (F i b) (J j)
  have he := A.map_sum g
  have hl : A (fun i => ∑ b, g i b) =
      (Matrix.of fun i j => ∑ b : Bool, C i b * M (F i b) (J j)).det := by
    change (Matrix.of fun i j => (∑ b, g i b) j).det = _
    simp only [Finset.sum_apply, g]
  rw [hl] at he
  rw [he]
  apply sum_congr rfl
  intro f _
  exact A.map_smul_univ (fun i => C i (f i)) (fun i j => M (F i (f i)) (J j))

def lowerRows (a : Seq) (M : Matrix ℕ ℕ ℝ) : Matrix ℕ ℕ ℝ :=
  fun n j => M n j + if n = 0 then 0 else a n * M (n-1) j

def upperRows (b : Seq) (M : Matrix ℕ ℕ ℝ) : Matrix ℕ ℕ ℝ :=
  fun n j => M n j + b n * M (n+1) j

def lowerChoice (a : Seq) (n : ℕ) (b : Bool) : ℝ :=
  if b then (if n = 0 then 0 else a n) else 1
def lowerIndex (n : ℕ) (b : Bool) : ℕ := if b then n-1 else n

theorem lowerRows_expansion {k : ℕ} (a : Seq) (M : Matrix ℕ ℕ ℝ) (I J : Fin k → ℕ) :
    ((lowerRows a M).submatrix I J).det =
      ∑ f : Fin k → Bool, (∏ i, lowerChoice a (I i) (f i)) *
        (M.submatrix (fun i => lowerIndex (I i) (f i)) J).det := by
  rw [← binary_row_expansion]
  congr 1
  ext i j
  simp only [Matrix.submatrix_apply, lowerRows, Matrix.of_apply, Fintype.sum_bool,
    lowerChoice, lowerIndex, Bool.false_eq_true, ite_false, ite_true, one_mul]
  split_ifs <;> ring

theorem lowerIndex_monotone {k : ℕ} (I : Fin k → ℕ) (hI : StrictMono I) (f : Fin k → Bool) :
    Monotone (fun i => lowerIndex (I i) (f i)) := by
  intro i j hij
  by_cases he : i = j
  · subst j; exact le_rfl
  · have hi := hI (lt_of_le_of_ne hij he)
    simp only [lowerIndex]
    split_ifs <;> omega

theorem lowerRows_TN {a : Seq} (ha : ∀ n, 0 < a n) {M : Matrix ℕ ℕ ℝ} (hM : TN M) :
    TN (lowerRows a M) := by
  intro k I J hI hJ
  rw [lowerRows_expansion]
  apply sum_nonneg
  intro f _
  apply mul_nonneg
  · apply prod_nonneg
    intro i _
    have hp := (ha (I i)).le
    unfold lowerChoice
    split_ifs <;> positivity
  · exact hM.monotone_rows _ J (lowerIndex_monotone I hI f) hJ

theorem lowerRows_BTP {p q : ℕ} {a : Seq} (ha : ∀ n, 0 < a n)
    {M : Matrix ℕ ℕ ℝ} (hM : BandedTP p q M) : BandedTP (p+1) q (lowerRows a M) := by
  refine ⟨lowerRows_TN ha hM.1, ?_⟩
  intro k I J hI hJ hadm
  rw [lowerRows_expansion]
  have hn : ∀ f : Fin k → Bool, 0 ≤ (∏ i, lowerChoice a (I i) (f i)) *
      (M.submatrix (fun i => lowerIndex (I i) (f i)) J).det := by
    intro f
    apply mul_nonneg
    · apply prod_nonneg
      intro i _
      have hp := (ha (I i)).le
      unfold lowerChoice
      split_ifs <;> positivity
    · exact TN.monotone_rows hM.1 _ J (lowerIndex_monotone I hI f) hJ
  apply sum_pos' (fun f _ => hn f)
  let f : Fin k → Bool := fun i => decide (J i < I i)
  refine ⟨f, mem_univ f, mul_pos ?_ ?_⟩
  · apply prod_pos
    intro i _
    by_cases hi : J i < I i
    · simp [f, lowerChoice, hi, show I i ≠ 0 by omega, ha]
    · simp [f, lowerChoice, hi]
  · apply hM.2 _ J ?_ hJ ?_
    · intro i j hij
      have hi := hI hij
      have hj := hJ hij
      simp only [lowerIndex, f, decide_eq_true_eq]
      split_ifs <;> omega
    · intro i
      have hi := hadm i
      simp only [lowerIndex, f, decide_eq_true_eq]
      split_ifs <;> omega

def upperChoice (b : Seq) (n : ℕ) (c : Bool) : ℝ := if c then b n else 1
def upperIndex (n : ℕ) (b : Bool) : ℕ := if b then n+1 else n

theorem upperRows_expansion {k : ℕ} (b : Seq) (M : Matrix ℕ ℕ ℝ) (I J : Fin k → ℕ) :
    ((upperRows b M).submatrix I J).det =
      ∑ f : Fin k → Bool, (∏ i, upperChoice b (I i) (f i)) *
        (M.submatrix (fun i => upperIndex (I i) (f i)) J).det := by
  rw [← binary_row_expansion]
  congr 1
  ext i j
  simp [upperRows, upperChoice, upperIndex, add_comm]

theorem upperIndex_monotone {k : ℕ} (I : Fin k → ℕ) (hI : StrictMono I) (f : Fin k → Bool) :
    Monotone (fun i => upperIndex (I i) (f i)) := by
  intro i j hij
  by_cases he : i = j
  · subst j; exact le_rfl
  · have hi := hI (lt_of_le_of_ne hij he)
    simp only [upperIndex]
    split_ifs <;> omega

theorem upperRows_TN {b : Seq} (hb : ∀ n, 0 < b n) {M : Matrix ℕ ℕ ℝ} (hM : TN M) :
    TN (upperRows b M) := by
  intro k I J hI hJ
  rw [upperRows_expansion]
  apply sum_nonneg
  intro f _
  apply mul_nonneg
  · apply prod_nonneg
    intro i _
    have hp := (hb (I i)).le
    unfold upperChoice
    split_ifs <;> positivity
  · exact hM.monotone_rows _ J (upperIndex_monotone I hI f) hJ

theorem upperRows_BTP {p q : ℕ} {b : Seq} (hb : ∀ n, 0 < b n)
    {M : Matrix ℕ ℕ ℝ} (hM : BandedTP p q M) : BandedTP p (q+1) (upperRows b M) := by
  refine ⟨upperRows_TN hb hM.1, ?_⟩
  intro k I J hI hJ hadm
  rw [upperRows_expansion]
  have hn : ∀ f : Fin k → Bool, 0 ≤ (∏ i, upperChoice b (I i) (f i)) *
      (M.submatrix (fun i => upperIndex (I i) (f i)) J).det := by
    intro f
    apply mul_nonneg
    · apply prod_nonneg
      intro i _
      have hp := (hb (I i)).le
      unfold upperChoice
      split_ifs <;> positivity
    · exact TN.monotone_rows hM.1 _ J (upperIndex_monotone I hI f) hJ
  apply sum_pos' (fun f _ => hn f)
  let f : Fin k → Bool := fun i => decide (I i < J i)
  refine ⟨f, mem_univ f, mul_pos ?_ ?_⟩
  · apply prod_pos
    intro i _
    by_cases hi : I i < J i <;> simp [f, upperChoice, hi, hb]
  · apply hM.2 _ J ?_ hJ ?_
    · intro i j hij
      have hi := hI hij
      have hj := hJ hij
      simp only [upperIndex, f, decide_eq_true_eq]
      split_ifs <;> omega
    · intro i
      have hi := hadm i
      simp only [upperIndex, f, decide_eq_true_eq]
      split_ifs <;> omega

#print axioms lowerRows_BTP
#print axioms upperRows_BTP
end BTP.Toeplitz
