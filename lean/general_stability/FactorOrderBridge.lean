import ActualAnalyticLDU
import FullPositiveTransfer

/-! Identification of the left-to-right Banach factor lists with the
right-indexed genuine matrix products used for triangular inverse rows. -/
noncomputable section
open scoped BigOperators
namespace BTP.GeneralStability
open BTP BTP.Stability.BandLDU

/-- Legacy factors are numbered from the right. -/
def reversedEntries {p : ℕ} (a : Fin p → Seq) : Entries :=
  fun k n => if h : k<p then a (Fin.rev ⟨k,h⟩) n else 0

theorem ofFn_rev (p : ℕ) (a : Fin p → Seq) :
    List.ofFn (fun i : Fin p => a i.rev) = (List.ofFn a).reverse := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_ofFn,List.getElem_reverse,List.length_ofFn]
    congr 1
    apply Fin.ext
    simp only [Fin.rev]
    omega

theorem productCoefficient_reverse (a : ℕ → Seq) (p d j : ℕ) :
    productCoefficient (List.ofFn (fun i : Fin p => a i.val)).reverse d j =
      entry (fun k n => a k n) p (j+d) d := by
  induction p generalizing d j with
  | zero =>
    cases d <;> simp [productCoefficient,entry]
  | succ p ih =>
    rw [List.ofFn_succ']
    simp only [List.concat_eq_append,List.reverse_append,List.reverse_cons,List.reverse_nil,
      List.nil_append,Fin.val_castSucc,Fin.val_last,List.singleton_append]
    cases d with
    | zero => simp
    | succ d =>
      simp only [productCoefficient,BoundedContinuousFunction.add_apply,
        BoundedContinuousFunction.mul_apply,translate_apply,ih,entry]
      congr 2

theorem productCoefficient_reversedEntries {p : ℕ} (a : Fin p → Seq) (d j : ℕ) :
    productCoefficient (List.ofFn a) d j=entry (reversedEntries a) p (j+d) d := by
  let b : ℕ → Seq := fun k => if h : k<p then a (Fin.rev ⟨k,h⟩) else 0
  have hb : (fun k n => b k n)=reversedEntries a := by
    funext k n
    dsimp [b,reversedEntries]
    split_ifs <;> rfl
  have hl : (List.ofFn (fun i : Fin p => b i.val)).reverse=List.ofFn a := by
    have he : List.ofFn (fun i : Fin p => b i.val)=List.ofFn (fun i : Fin p => a i.rev) := by
      congr 1
      funext i
      simp [b,i.isLt]
    rw [he,ofFn_rev,List.reverse_reverse]
  rw [←hl,productCoefficient_reverse,hb]

theorem reversed_product_band {p : ℕ} (a : Fin p → Seq) (M : ℝ) (hM : 0≤M)
    (ha : ∀ k<p, ∀ n, 0<n → |reversedEntries a k n|≤M) :
    actualLowerCoordinates (reversedEntries a) p M hM ha=lowerProductBand a := by
  funext r
  apply BoundedContinuousFunction.ext
  intro j
  change entry (reversedEntries a) p (j+(r.val+1)) (r.val+1)=
    productCoefficient (List.ofFn a) (r.val+1) j
  exact (productCoefficient_reversedEntries a (r.val+1) j).symm

theorem reversed_factor_base {p q : ℕ} (a : Fin p → Seq) (d : Seq) (b : Fin q → Seq)
    (M : ℝ) (hM : 0≤M)
    (ha : ∀ k<p, ∀ n, 0<n → |reversedEntries a k n|≤M)
    (hb : ∀ k<q, ∀ n, 0<n → |reversedEntries b k n|≤M) :
    actualBase (reversedEntries a) (reversedEntries b) p q d M hM ha hb=factorBase a d b := by
  simp only [actualBase,factorBase,reversed_product_band]

#print axioms productCoefficient_reversedEntries
#print axioms reversed_factor_base
end BTP.GeneralStability
