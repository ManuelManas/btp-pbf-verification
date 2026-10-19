import RelativeUniquenessCore
import ArbitraryDiagonalBridge

/-! Global uniqueness of positive factors with fixed initial entries,
including the diagonal and both triangular sides. -/
noncomputable section
set_option maxHeartbeats 1000000
open Finset Matrix
open scoped BigOperators
namespace BTP.RelativeStability
open BTP BTP.GeneralStability BTP.SemiInfinite BTP.InverseBounds

theorem sameProduct_coefficients {p : ℕ} {a b : Entries} (h : SameProduct p a b)
    (n r : ℕ) (hr : r≤n) : entry a p n r=entry b p n r := by
  let i : Fin (n+1):=⟨n,by omega⟩
  let j : Fin (n+1):=⟨n-r,by omega⟩
  have hh:=congrArg (fun M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ=>M i j) (h (n+1))
  simp only [lowerProduct_entry,i,j,show n-r≤n by omega,↓reduceIte,show n-(n-r)=r by omega] at hh
  exact hh

theorem relativeFactorBase_fullEntry_finite {p q N : ℕ}
    (a : Fin p → ℕ → ℝ) (d : ℕ → ℝ) (b : Fin q → ℕ → ℝ) (i j : Fin N) :
    rawFullEntry (relativeFactorBase a) d (relativeFactorBase b) i.val j.val=
      triangularSections p q (rawReverse (extendRaw a) p) (rawReverse (extendRaw b) q) d N i j := by
  rw [rawFullEntry_fin,triangularSections,Matrix.mul_apply]
  simp only [Matrix.mul_diagonal,Matrix.transpose_apply]
  apply sum_congr rfl
  intro k _
  have ha:=congrArg (fun M : Matrix (Fin N) (Fin N) ℝ=>M i k)
    (rawUnitEntry_productBand_finite (extendRaw a) p N)
  have hb:=congrArg (fun M : Matrix (Fin N) (Fin N) ℝ=>M j k)
    (rawUnitEntry_productBand_finite (extendRaw b) q N)
  rw [←ha,←hb]
  rfl

/-- Express the initial-data condition in the opposite factor ordering. -/
theorem rawReverse_initial {p : ℕ} (a a' : Fin p → ℕ → ℝ)
    (hinit : ∀ i n,0<n → n<p-i.val → a i n=a' i n) :
    ∀ j<p,∀ n,0<n → n≤j →
      rawReverse (extendRaw a) p j n=rawReverse (extendRaw a') p j n := by
  intro j hj n hn hnj
  have hlt : p-1-j<p := by omega
  have hh:=hinit ⟨p-1-j,hlt⟩ n hn (by dsimp;omega)
  simpa only [rawReverse,extendRaw,hlt,↓reduceDIte] using hh

theorem rawReverse_unique_to_factors {p : ℕ} (a a' : Fin p → ℕ → ℝ)
    (h : ∀ n j,0<n → j<p →
      rawReverse (extendRaw a) p j n=rawReverse (extendRaw a') p j n) :
    ∀ i n,0<n → a i n=a' i n := by
  intro i n hn
  have hj : p-1-i.val<p := by have:=i.isLt;omega
  have hh:=h n (p-1-i.val) hn hj
  simpa only [rawReverse,show p-1-(p-1-i.val)=i.val by have:=i.isLt;omega,
    extendRaw,i.isLt,↓reduceDIte] using hh

/-- Global, not merely nearby, uniqueness. Every factor entry with a
positive row index and every diagonal entry agrees. There are no norm,
growth, geometric-decay, or smallness assumptions in this statement. -/
theorem relative_full_factors_global_unique {p q : ℕ}
    (a a' : Fin p → ℕ → ℝ) (d d' : ℕ → ℝ) (b b' : Fin q → ℕ → ℝ)
    (ha : ∀ i n,0<n → 0<a i n) (hd : ∀ n,0<d n) (hb : ∀ i n,0<n → 0<b i n)
    (hai : ∀ i n,0<n → n<p-i.val → a i n=a' i n)
    (hbi : ∀ i n,0<n → n<q-i.val → b i n=b' i n)
    (hprod : ∀ i j,rawFullEntry (relativeFactorBase a) d (relativeFactorBase b) i j=
      rawFullEntry (relativeFactorBase a') d' (relativeFactorBase b') i j) :
    d=d' ∧ (∀ i n,0<n → a i n=a' i n) ∧ (∀ i n,0<n → b i n=b' i n) := by
  let ar:=rawReverse (extendRaw a) p
  let ar':=rawReverse (extendRaw a') p
  let br:=rawReverse (extendRaw b) q
  let br':=rawReverse (extendRaw b') q
  have hs : ∀ N,triangularSections p q ar' br' d' N=triangularSections p q ar br d N := by
    intro N
    ext i j
    rw [←relativeFactorBase_fullEntry_finite a' d' b' i j,
      ←relativeFactorBase_fullEntry_finite a d b i j]
    exact (hprod i.val j.val).symm
  have he : d'=d := normalized_diagonal_unique p q ar ar' br br' d d'
    (fun n=>ne_of_gt (hd n)) hs
  refine ⟨he.symm,?_⟩
  subst d'
  obtain ⟨hL,hU⟩:=normalized_products_unique p q ar ar' br br' d
    (fun n=>ne_of_gt (hd n)) hs
  constructor
  · apply rawReverse_unique_to_factors a a'
    apply positive_factors_unique_from_entries p ar ar'
    · intro j hj n hn
      have hlt : p-1-j<p := by omega
      change 0<extendRaw a (p-1-j) n
      simpa only [extendRaw,hlt,↓reduceDIte] using ha ⟨p-1-j,hlt⟩ n hn
    · exact rawReverse_initial a a' hai
    · intro n r hr
      exact (sameProduct_coefficients hL n r hr).symm
  · apply rawReverse_unique_to_factors b b'
    apply positive_factors_unique_from_entries q br br'
    · intro j hj n hn
      have hlt : q-1-j<q := by omega
      change 0<extendRaw b (q-1-j) n
      simpa only [extendRaw,hlt,↓reduceDIte] using hb ⟨q-1-j,hlt⟩ n hn
    · exact rawReverse_initial b b' hbi
    · intro n r hr
      exact (sameProduct_coefficients hU n r hr).symm

#print axioms relative_full_factors_global_unique
end BTP.RelativeStability
