import RelativeFullTransfer
import RelativeNormalizedControl
import Lemma24

/-! Global uniqueness with the prescribed initial entries. The argument
is algebraic and uses neither boundedness nor closeness of factors. -/
noncomputable section
set_option maxHeartbeats 1000000
open Finset Matrix
open scoped BigOperators
namespace BTP.RelativeStability
open BTP BTP.GeneralStability BTP.SemiInfinite BTP.InverseBounds

/-- Actual coefficients never use the fictitious row-zero subdiagonal. -/
theorem entry_congr_positive_rows (a b : Entries) (p n r : ℕ) (hr : r≤n)
    (h : ∀ j < p,∀ m,0<m → m≤n → a j m=b j m) : entry a p n r=entry b p n r := by
  induction p generalizing n r with
  | zero => rfl
  | succ p ih =>
    cases r with
    | zero => rfl
    | succ r =>
      simp only [entry]
      rw [ih n (r+1) hr (fun j hj m hm hmn=>h j (by omega) m hm hmn),
        h p (by omega) n (by omega) le_rfl,
        ih (n-1) r (by omega) (fun j hj m hm hmn=>h j (by omega) m hm (by omega))]

/-- Ordered positive bidiagonal factors are globally determined by their
product and their finite triangular set of initial entries. Factor
indices here run from the right, as in the original finite row theorem. -/
theorem positive_factors_unique_from_entries (p : ℕ) (a b : Entries)
    (ha : ∀ j < p,∀ n,0<n → 0<a j n)
    (hinit : ∀ j < p,∀ n,0<n → n≤j → a j n=b j n)
    (hprod : ∀ n r,r≤n → entry a p n r=entry b p n r) :
    ∀ n j,0<n → j<p → a j n=b j n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro j hn hj
    by_cases hnj : n≤j
    · exact hinit j hj n hn hnj
    · let k:=min p n
      have hjk : j<k := by dsimp [k];omega
      have hold (r : Fin k) (s : ℕ) (hs : s<p) :
          entry a s (n-1) r.val=entry b s (n-1) r.val := by
        apply entry_congr_positive_rows _ _ _ _ _ (by have:=r.isLt;dsimp [k] at *;omega)
        intro l hl m hm hmn
        exact ih m (by omega) l hm (by omega)
      have hrow (r : Fin k) :
          (∑ s ∈ range p,a s n*entry a s (n-1) r.val)=
          ∑ s ∈ range p,b s n*entry a s (n-1) r.val := by
        calc
          _=entry a p n (r.val+1) := (entry_row a p n r.val).symm
          _=entry b p n (r.val+1) := hprod n _ (by have:=r.isLt;dsimp [k] at *;omega)
          _=∑ s ∈ range p,b s n*entry a s (n-1) r.val := by
            rw [entry_row]
            apply sum_congr rfl
            intro s hs
            rw [hold r s (mem_range.mp hs)]
      have hhead (r : Fin k) :
          (∑ s ∈ range k,a s n*entry a s (n-1) r.val)=
          ∑ s ∈ range k,b s n*entry a s (n-1) r.val := by
        have ht : (∑ s ∈ Ico k p,a s n*entry a s (n-1) r.val)=
            ∑ s ∈ Ico k p,b s n*entry a s (n-1) r.val := by
          apply sum_congr rfl
          intro s hs
          have hs':=mem_Ico.mp hs
          rw [hinit s hs'.2 n hn (by dsimp [k] at hs';omega)]
        have hh:=hrow r
        rw [←sum_range_add_sum_Ico _ (min_le_left p n),
          ←sum_range_add_sum_Ico _ (min_le_left p n)] at hh
        change (∑ s ∈ range k,a s n*entry a s (n-1) r.val)+_= _ at hh
        rw [ht] at hh
        exact add_right_cancel hh
      have hvec : rowMatrix a k n *ᵥ (fun s : Fin k=>a s.val n)=
          rowMatrix a k n *ᵥ (fun s : Fin k=>b s.val n) := by
        funext r
        simp only [Matrix.mulVec,dotProduct,rowMatrix]
        rw [Fin.sum_univ_eq_sum_range (fun s=>entry a s (n-1) r.val*a s n),
          Fin.sum_univ_eq_sum_range (fun s=>entry a s (n-1) r.val*b s n)]
        simpa only [mul_comm] using hhead r
      have hinj : Function.Injective (fun x : Fin k→ℝ=>rowMatrix a k n *ᵥ x) :=
        Matrix.mulVec_injective_iff_isUnit.mpr
          ((Matrix.isUnit_iff_isUnit_det (rowMatrix a k n)).mpr (isUnit_iff_ne_zero.mpr
            (ne_of_gt (rowMatrix_det_pos a k n (min_le_right p n)
              (fun i hi m _ him=>ha i (by dsimp [k] at hi;omega) m (by omega))))))
      exact congrFun (hinj hvec) ⟨j,hjk⟩

#print axioms positive_factors_unique_from_entries
end BTP.RelativeStability
