import PBFMinors

/-! Structural zero minors: this connects the auxiliary TN-and-positive-minors
predicate to exactly the BTP convention used in the manuscript. -/

open Matrix Finset
noncomputable section
namespace BTP.Toeplitz

theorem perm_prefix_crossing {k : ℕ} (σ : Equiv.Perm (Fin k)) (i : Fin k) :
    ∃ j : Fin k, j ≤ i ∧ i ≤ σ j := by
  by_contra h
  push Not at h
  let f : Fin (i.val+1) → Fin i.val := fun j =>
    ⟨(σ ⟨j.val, by omega⟩).val, h ⟨j.val, by omega⟩ (by change j.val ≤ i.val; omega)⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Fin.ext
    have he : σ ⟨a.val, by omega⟩ = σ ⟨b.val, by omega⟩ := by
      apply Fin.ext
      exact congrArg (fun z : Fin i.val => z.val) hab
    exact congrArg (fun z : Fin k => z.val) (σ.injective he)
  have hc := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin] at hc
  omega

theorem sorted_bound_of_permutation {k : ℕ} (I J : Fin k → ℕ)
    (hI : Monotone I) (hJ : Monotone J) (σ : Equiv.Perm (Fin k)) (p : ℕ)
    (hb : ∀ j, I (σ j) ≤ J j + p) : ∀ i, I i ≤ J i+p := by
  intro i
  obtain ⟨j, hji, hij⟩ := perm_prefix_crossing σ i
  exact (hI hij).trans ((hb j).trans (Nat.add_le_add_right (hJ hji) p))

def Band (p q : ℕ) (M : Matrix ℕ ℕ ℝ) : Prop :=
  ∀ i j, (i > j+p ∨ j > i+q) → M i j = 0

/-- The manuscript's definition: strict positivity only on admissible minors. -/
def StrictBandTP (p q : ℕ) (M : Matrix ℕ ℕ ℝ) : Prop :=
  ∀ {k : ℕ} (I J : Fin k → ℕ), StrictMono I → StrictMono J →
    Admissible p q I J → 0 < (M.submatrix I J).det

theorem nonzero_minor_admissible {p q k : ℕ} {M : Matrix ℕ ℕ ℝ}
    (hM : Band p q M) (I J : Fin k → ℕ) (hI : StrictMono I) (hJ : StrictMono J)
    (hdet : (M.submatrix I J).det ≠ 0) : Admissible p q I J := by
  have hex : ∃ σ : Equiv.Perm (Fin k), ∀ i, M (I (σ i)) (J i) ≠ 0 := by
    by_contra h
    push Not at h
    apply hdet
    rw [Matrix.det_apply']
    apply sum_eq_zero
    intro σ _
    obtain ⟨i, hi⟩ := h σ
    have hz : (∏ a, (M.submatrix I J) (σ a) a) = 0 := prod_eq_zero (mem_univ i) hi
    rw [hz, mul_zero]
  obtain ⟨σ, hσ⟩ := hex
  have he : ∀ j, I (σ j) ≤ J j+p ∧ J j ≤ I (σ j)+q := by
    intro j
    constructor
    · by_contra h
      exact hσ j (hM _ _ (Or.inl (Nat.lt_of_not_ge h)))
    · by_contra h
      exact hσ j (hM _ _ (Or.inr (Nat.lt_of_not_ge h)))
  have hlow := sorted_bound_of_permutation I J hI.monotone hJ.monotone σ p (fun j => (he j).1)
  have hupp := sorted_bound_of_permutation J I hJ.monotone hI.monotone σ.symm q
    (fun j => by simpa using (he (σ.symm j)).2)
  exact fun i => ⟨hlow i, hupp i⟩

theorem inadmissible_minor_zero {p q k : ℕ} {M : Matrix ℕ ℕ ℝ}
    (hM : Band p q M) (I J : Fin k → ℕ) (hI : StrictMono I) (hJ : StrictMono J)
    (ha : ¬ Admissible p q I J) : (M.submatrix I J).det = 0 := by
  by_contra h
  exact ha (nonzero_minor_admissible hM I J hI hJ h)

theorem BandedTP_iff_strict {p q : ℕ} {M : Matrix ℕ ℕ ℝ} (hM : Band p q M) :
    BandedTP p q M ↔ StrictBandTP p q M := by
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    intro k I J hI hJ
    by_cases ha : Admissible p q I J
    · exact (h I J hI hJ ha).le
    · rw [inadmissible_minor_zero hM I J hI hJ ha]

theorem symbolMatrix_band (p q : ℕ) (P : Polynomial ℝ) (hdeg : P.natDegree ≤ p+q) :
    Band p q (symbolMatrix q P) := by
  intro i j h
  unfold symbolMatrix
  by_cases hj : j ≤ i+q
  · rw [ite_eq_left hj]
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    rcases h with h | h
    · omega
    · omega
  · simp [hj]

#print axioms inadmissible_minor_zero
#print axioms BandedTP_iff_strict
end BTP.Toeplitz
