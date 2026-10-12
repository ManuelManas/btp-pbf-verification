import BidiagonalSwap

/-! Finite lists of actual semi-infinite operators. List lengths record both
bandwidths, and all bounds are uniform in the row index. -/

noncomputable section
namespace BTP.Toeplitz

def lowerProduct (a : List Seq) : Op := (a.map lower).prod
def upperProduct (u : List Seq) : Op := (u.map upper).prod
def unitUpperProduct (b : List Seq) : Op := (b.map unitUpper).prod

@[simp] theorem lowerProduct_nil : lowerProduct [] = 1 := rfl
@[simp] theorem upperProduct_nil : upperProduct [] = 1 := rfl
@[simp] theorem unitUpperProduct_nil : unitUpperProduct [] = 1 := rfl
@[simp] theorem lowerProduct_cons (a : Seq) (as : List Seq) :
    lowerProduct (a :: as) = lower a * lowerProduct as := rfl
@[simp] theorem upperProduct_cons (u : Seq) (us : List Seq) :
    upperProduct (u :: us) = upper u * upperProduct us := rfl
@[simp] theorem unitUpperProduct_cons (b : Seq) (bs : List Seq) :
    unitUpperProduct (b :: bs) = unitUpper b * unitUpperProduct bs := rfl

/-- Move one lower factor leftwards across the prescribed upper factors. -/
theorem move_one_lower (us : List Seq) (a : Seq)
    (hu : ∀ u ∈ us, BoundedPositive u) (ha : BoundedPositive a) :
    ∃ b : Seq, ∃ vs : List Seq,
      BoundedPositive b ∧ (∀ v ∈ vs, BoundedPositive v) ∧
      vs.length = us.length ∧ upperProduct us * lower a = lower b * upperProduct vs := by
  induction us with
  | nil => exact ⟨a, [], ha, by simp, rfl, by simp⟩
  | cons u us ih =>
    obtain ⟨b, vs, hb, hv, hlen, he⟩ := ih (fun v hv => hu v (by simp [hv]))
    obtain ⟨c, d, hc, hd, hswap⟩ := bounded_positive_exchange (hu u (by simp)) hb
    refine ⟨c, d :: vs, hc, ?_, by simp [hlen], ?_⟩
    · intro v hv'
      rcases List.mem_cons.mp hv' with h | h
      · simpa [h] using hd
      · exact hv v h
    · simp only [upperProduct_cons]
      calc
        (upper u * upperProduct us) * lower a = upper u * (upperProduct us * lower a) := mul_assoc _ _ _
        _ = upper u * (lower b * upperProduct vs) := by rw [he]
        _ = (upper u * lower b) * upperProduct vs := (mul_assoc _ _ _).symm
        _ = (lower c * upper d) * upperProduct vs := by rw [hswap]
        _ = lower c * (upper d * upperProduct vs) := mul_assoc _ _ _

/-- All lower factors are moved, one at a time, in their original order. -/
theorem reorder_factors (us as : List Seq)
    (hu : ∀ u ∈ us, BoundedPositive u) (ha : ∀ a ∈ as, BoundedPositive a) :
    ∃ bs vs : List Seq,
      (∀ b ∈ bs, BoundedPositive b) ∧ (∀ v ∈ vs, BoundedPositive v) ∧
      bs.length = as.length ∧ vs.length = us.length ∧
      upperProduct us * lowerProduct as = lowerProduct bs * upperProduct vs := by
  induction as generalizing us with
  | nil => exact ⟨[], us, by simp, hu, rfl, rfl, by simp⟩
  | cons a as ih =>
    obtain ⟨b, vs, hb, hv, hlenv, hmove⟩ := move_one_lower us a hu (ha a (by simp))
    obtain ⟨cs, ws, hc, hw, hlenc, hlenw, hrest⟩ :=
      ih vs hv (fun c hc => ha c (by simp [hc]))
    refine ⟨b :: cs, ws, ?_, hw, by simp [hlenc], hlenw.trans hlenv, ?_⟩
    · intro c hc'
      rcases List.mem_cons.mp hc' with h | h
      · simpa [h] using hb
      · exact hc c h
    · simp only [lowerProduct_cons]
      calc
        upperProduct us * (lower a * lowerProduct as) =
            (upperProduct us * lower a) * lowerProduct as := (mul_assoc _ _ _).symm
        _ = (lower b * upperProduct vs) * lowerProduct as := by rw [hmove]
        _ = lower b * (upperProduct vs * lowerProduct as) := mul_assoc _ _ _
        _ = lower b * (lowerProduct cs * upperProduct ws) := by rw [hrest]
        _ = (lower b * lowerProduct cs) * upperProduct ws := (mul_assoc _ _ _).symm

theorem diagonal_one : diagonal (fun _ => 1) = 1 := by ext x n; simp

theorem diagonal_mul (d e : Seq) : diagonal d * diagonal e = diagonal (fun n => d n * e n) := by
  ext x n
  change d n * (e n * x n) = (d n * e n) * x n
  ring

theorem upper_mul_diagonal (u d : Seq) (hu : ∀ n, u n ≠ 0) (hd : ∀ n, d n ≠ 0) :
    upper u * diagonal d = diagonal (fun n => u n * d n) *
      unitUpper (fun n => d (n+1) / (u n * d n)) := by
  ext x n
  change u n * (d n * x n) + d (n+1) * x (n+1) =
    (u n * d n) * (x n + (d (n+1) / (u n * d n)) * x (n+1))
  field_simp [hu n, hd n]

/-- Extract a single diagonal, leaving exactly the same number of unit upper factors. -/
theorem normalize_upper_factors (us : List Seq) (hu : ∀ u ∈ us, BoundedPositive u) :
    ∃ d : Seq, ∃ bs : List Seq,
      BoundedPositive d ∧ (∀ b ∈ bs, BoundedPositive b) ∧ bs.length = us.length ∧
      upperProduct us = diagonal d * unitUpperProduct bs := by
  induction us with
  | nil => exact ⟨fun _ => 1, [], boundedPositive_const zero_lt_one, by simp, rfl,
      by simp [diagonal_one]⟩
  | cons u us ih =>
    obtain ⟨d, bs, hd, hb, hlen, he⟩ := ih (fun v hv => hu v (by simp [hv]))
    have hup := hu u (by simp)
    let b : Seq := fun n => d (n+1) / (u n * d n)
    have hbp : BoundedPositive b := (hd.comp (fun n => n+1)).div (hup.mul hd)
    refine ⟨fun n => u n * d n, b :: bs, hup.mul hd, ?_, by simp [hlen], ?_⟩
    · intro v hv
      rcases List.mem_cons.mp hv with h | h
      · simpa [h] using hbp
      · exact hb v h
    · simp only [upperProduct_cons, unitUpperProduct_cons]
      rw [he, ← mul_assoc, upper_mul_diagonal u d (fun n => (hup.pos n).ne')
        (fun n => (hd.pos n).ne'), mul_assoc]

theorem constant_diagonal_commutes (ω : ℝ) (A : Op) :
    diagonal (fun _ => ω) * A = A * diagonal (fun _ => ω) := by
  ext x n
  change (ω • A x) n = (A (ω • x)) n
  rw [A.map_smul]

/-- A normalized PBF, with entry bounds for every factor and for the diagonal. -/
def HasBoundedPBF (p q : ℕ) (T : Op) : Prop :=
  ∃ as bs : List Seq, ∃ d : Seq,
    as.length = p ∧ bs.length = q ∧
    (∀ a ∈ as, BoundedPositive a) ∧ (∀ b ∈ bs, BoundedPositive b) ∧
    BoundedPositive d ∧ T = lowerProduct as * diagonal d * unitUpperProduct bs

/-- Constructive upper--lower to lower--diagonal--upper reordering, for any finite lengths. -/
theorem upper_lower_has_bounded_PBF (ω : ℝ) (hω : 0 < ω) (us as : List Seq)
    (hu : ∀ u ∈ us, BoundedPositive u) (ha : ∀ a ∈ as, BoundedPositive a) :
    HasBoundedPBF as.length us.length
      (diagonal (fun _ => ω) * (upperProduct us * lowerProduct as)) := by
  obtain ⟨ls, vs, hl, hv, hlenl, hlenv, he⟩ := reorder_factors us as hu ha
  obtain ⟨d, bs, hd, hb, hlenb, hn⟩ := normalize_upper_factors vs hv
  refine ⟨ls, bs, fun n => ω * d n, hlenl, hlenb.trans hlenv, hl, hb,
    (boundedPositive_const hω).mul hd, ?_⟩
  rw [he, hn]
  calc
    diagonal (fun _ => ω) * (lowerProduct ls * (diagonal d * unitUpperProduct bs)) =
      (diagonal (fun _ => ω) * lowerProduct ls) * (diagonal d * unitUpperProduct bs) :=
        (mul_assoc _ _ _).symm
    _ = (lowerProduct ls * diagonal (fun _ => ω)) * (diagonal d * unitUpperProduct bs) := by
      rw [constant_diagonal_commutes]
    _ = (lowerProduct ls * diagonal (fun n => ω * d n)) * unitUpperProduct bs := by
      simp only [mul_assoc, ← diagonal_mul]

#print axioms reorder_factors
#print axioms upper_lower_has_bounded_PBF
end BTP.Toeplitz
