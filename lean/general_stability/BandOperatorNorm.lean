import BandSpaces
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.Banach

/-! Genuine bounded operators on ℓ² and the fixed-band coefficient norm. -/
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 1000000
namespace BTP.GeneralStability

abbrev L2 := lp (fun _ : ℕ => ℝ) 2

private theorem l2_sum_sq_le (x : L2) (s : Finset ℕ) :
    ∑ n ∈ s, ‖x n‖^2  ≤  ‖x‖^2 := by
  simpa using lp.sum_rpow_le_norm_rpow (p:=2) (by norm_num) x s

private theorem l2_mem_of_sums (f : ℕ → ℝ) (C : ℝ)
    (h : ∀ s : Finset ℕ, ∑ n ∈ s, ‖f n‖^2  ≤  C) : Memℓp f 2 := by
  apply memℓp_gen'
  simpa using h

private theorem l2_norm_le_of_sums (x : L2) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ s : Finset ℕ, ∑ n ∈ s, ‖x n‖^2  ≤  C^2) : ‖x‖ ≤ C := by
  apply lp.norm_le_of_forall_sum_le (p:=2) (by norm_num) hC
  simpa using h

private theorem shiftLeft_sums (d : ℕ) (x : L2) (s : Finset ℕ) :
    ∑ n ∈ s, ‖x (n+d)‖^2  ≤  ‖x‖^2 := by
  have he : (∑ n ∈ s, ‖x (n+d)‖^2)=∑ n ∈ s.image (fun n=>n+d), ‖x n‖^2 := by
    rw [Finset.sum_image]
    intro i _ j _ h
    dsimp at h
    omega
  rw [he]
  exact l2_sum_sq_le x _

private theorem shiftRight_sums (d : ℕ) (x : L2) (s : Finset ℕ) :
    ∑ n ∈ s, ‖(if d ≤ n then x (n-d) else 0 : ℝ)‖^2  ≤  ‖x‖^2 := by
  classical
  have he : (∑ n ∈ s, ‖(if d ≤ n then x (n-d) else 0 : ℝ)‖^2)=
      ∑ n ∈ (s.filter (fun n=>d ≤ n)).image (fun n=>n-d), ‖x n‖^2 := by
    rw [Finset.sum_image]
    · rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n _
      split_ifs  <;> simp
    · intro i hi j hj h
      dsimp at h
      have hi' := (Finset.mem_filter.mp hi).2
      have hj' := (Finset.mem_filter.mp hj).2
      omega
  rw [he]
  exact l2_sum_sq_le x _

/-- Translation towards the origin, with operator norm at most one. -/
def l2ShiftLeft (d : ℕ) : L2 →L[ℝ] L2 :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨fun n=>x (n+d),l2_mem_of_sums _ (‖x‖^2) (shiftLeft_sums d x)⟩
      map_add' := by intro x y; apply lp.ext; funext n; rfl
      map_smul' := by intro c x; apply lp.ext; funext n; rfl }
    1 (by
      intro x
      simpa using l2_norm_le_of_sums _ ‖x‖ (norm_nonneg x) (shiftLeft_sums d x))

/-- Translation away from the origin, filling the first d rows with zero. -/
def l2ShiftRight (d : ℕ) : L2 →L[ℝ] L2 :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨fun n=>if d ≤ n then x (n-d) else 0,
        l2_mem_of_sums _ (‖x‖^2) (shiftRight_sums d x)⟩
      map_add' := by
        intro x y; apply lp.ext; funext n
        change (if d ≤ n then x (n-d)+y (n-d) else 0)=
          (if d ≤ n then x (n-d) else 0)+(if d ≤ n then y (n-d) else 0)
        split_ifs  <;> simp
      map_smul' := by
        intro c x; apply lp.ext; funext n
        change (if d ≤ n then c*x (n-d) else 0)=c*(if d ≤ n then x (n-d) else 0)
        split_ifs  <;> simp }
    1 (by
      intro x
      simpa using l2_norm_le_of_sums _ ‖x‖ (norm_nonneg x) (shiftRight_sums d x))

@[simp] theorem l2ShiftLeft_apply (d : ℕ) (x : L2) (n : ℕ) :
    l2ShiftLeft d x n=x (n+d) := rfl
@[simp] theorem l2ShiftRight_apply (d : ℕ) (x : L2) (n : ℕ) :
    l2ShiftRight d x n=if d ≤ n then x (n-d) else 0 := rfl

theorem norm_l2ShiftLeft_le (d : ℕ) : ‖l2ShiftLeft d‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _
theorem norm_l2ShiftRight_le (d : ℕ) : ‖l2ShiftRight d‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- Multiplication by a bounded real diagonal sequence. -/
def l2Diagonal (a : Seq) : L2 →L[ℝ] L2 :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨fun n=>a n*x n,
        ((lp.memℓp x).norm.const_mul ‖a‖).mono (fun n=> by
          rw [norm_mul,Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right (BTP.Stability.boundedSequence_abs_le a n) (norm_nonneg _))⟩
      map_add' := by intro x y; apply lp.ext; funext n; change a n*(x n+y n)=a n*x n+a n*y n; ring
      map_smul' := by intro c x; apply lp.ext; funext n; change a n*(c*x n)=c*(a n*x n); ring }
    ‖a‖ (by
      intro x
      calc
        _  ≤  ‖(‖a‖ : ℝ) • x‖ := by
          apply lp.norm_mono (by norm_num : (2 : ENNReal)≠0)
          intro n
          change ‖a n*x n‖  ≤  ‖‖a‖*x n‖
          simp only [norm_mul,Real.norm_eq_abs]
          rw [abs_of_nonneg (norm_nonneg a)]
          exact mul_le_mul_of_nonneg_right (BTP.Stability.boundedSequence_abs_le a n) (abs_nonneg _)
        _ = ‖a‖*‖x‖ := by
          rw [lp.norm_const_smul (by norm_num : (2 : ENNReal)≠0)]
          simp)

@[simp] theorem l2Diagonal_apply (a : Seq) (x : L2) (n : ℕ) :
    l2Diagonal a x n=a n*x n := rfl

theorem norm_l2Diagonal_le (a : Seq) : ‖l2Diagonal a‖ ≤ ‖a‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg a) _

/-- The j-th coordinate unit vector in ℓ². -/
def l2Basis (j : ℕ) : L2 := lp.single 2 j 1

@[simp] theorem l2Basis_apply (j n : ℕ) : l2Basis j n=if n=j then 1 else 0 := by
  simp [l2Basis,lp.single_apply,Pi.single_apply]

@[simp] theorem norm_l2Basis (j : ℕ) : ‖l2Basis j‖=1 := by
  simp [l2Basis,lp.norm_single (by norm_num : (0:ENNReal) < 2)]

private theorem lowerDiagonal_basis (a : Seq) (d i j : ℕ) :
    ((l2ShiftRight d).comp (l2Diagonal a)) (l2Basis j) i=
      if i=j+d then a j else 0 := by
  simp only [ContinuousLinearMap.comp_apply,l2ShiftRight_apply,l2Diagonal_apply,l2Basis_apply]
  by_cases he : i=j+d
  · subst i
    simp
  · by_cases hi : d ≤ i
    · have hn : i-d≠j := by omega
      simp [hi,hn,he]
    · simp [hi,he]

private theorem upperDiagonal_basis (a : Seq) (d i j : ℕ) :
    ((l2Diagonal a).comp (l2ShiftLeft d)) (l2Basis j) i=
      if j=i+d then a i else 0 := by
  simp only [ContinuousLinearMap.comp_apply,l2ShiftLeft_apply,l2Diagonal_apply,l2Basis_apply]
  by_cases he : j=i+d
  · simp [he]
  · simp [he,Ne.symm he]

/-- Strict lower band, acting on ℓ² by its actual matrix entries. -/
def lowerBandOperator {m : ℕ} (E : LowerBand m) : L2 →L[ℝ] L2 :=
  ∑ r : Fin m, (l2ShiftRight (r.val+1)).comp (l2Diagonal (E r))

/-- Strict upper band, represented by transpose coordinates. -/
def upperBandOperator {m : ℕ} (E : LowerBand m) : L2 →L[ℝ] L2 :=
  ∑ r : Fin m, (l2Diagonal (E r)).comp (l2ShiftLeft (r.val+1))

theorem lowerBandOperator_basis {m : ℕ} (E : LowerBand m) (i j : ℕ) :
    lowerBandOperator E (l2Basis j) i=bandEntry E i j := by
  classical
  simp only [lowerBandOperator,sum_apply,lp.coeFn_sum,Finset.sum_apply,
    lowerDiagonal_basis]
  unfold bandEntry
  split_ifs with h
  · let r : Fin m := ⟨i-j-1,by omega⟩
    have he : i=j+(r.val+1) := by dsimp [r]; omega
    rw [Finset.sum_eq_single r]
    · rw [ite_eq_left he]
    · intro b _ hbr
      have hn : i≠j+(b.val+1) := by
        intro hb
        apply hbr
        apply Fin.ext
        dsimp [r]
        omega
      simp [hn]
    · simp
  · apply Finset.sum_eq_zero
    intro r _
    have hn : i≠j+(r.val+1) := by have := r.isLt; omega
    simp [hn]

theorem upperBandOperator_basis {m : ℕ} (E : LowerBand m) (i j : ℕ) :
    upperBandOperator E (l2Basis j) i=bandEntry E j i := by
  classical
  have hh := lowerBandOperator_basis E j i
  simpa only [lowerBandOperator,upperBandOperator,sum_apply,
    lp.coeFn_sum,Finset.sum_apply,lowerDiagonal_basis,upperDiagonal_basis] using hh

theorem norm_lowerBandOperator_le {m : ℕ} (E : LowerBand m) :
    ‖lowerBandOperator E‖ ≤ (m:ℝ)*‖E‖ := by
  calc
    _  ≤  ∑ r : Fin m, ‖(l2ShiftRight (r.val+1)).comp (l2Diagonal (E r))‖ := norm_sum_le _ _
    _  ≤  ∑ _r : Fin m, ‖E‖ := by
      apply Finset.sum_le_sum
      intro r _
      calc
        _  ≤  ‖l2ShiftRight (r.val+1)‖*‖l2Diagonal (E r)‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _  ≤  1*‖E r‖ := mul_le_mul (norm_l2ShiftRight_le _) (norm_l2Diagonal_le _) (norm_nonneg _) zero_le_one
        _  ≤  ‖E‖ := by simpa using norm_le_pi_norm E r
    _ = _ := by simp

theorem norm_upperBandOperator_le {m : ℕ} (E : LowerBand m) :
    ‖upperBandOperator E‖ ≤ (m:ℝ)*‖E‖ := by
  calc
    _  ≤  ∑ r : Fin m, ‖(l2Diagonal (E r)).comp (l2ShiftLeft (r.val+1))‖ := norm_sum_le _ _
    _  ≤  ∑ _r : Fin m, ‖E‖ := by
      apply Finset.sum_le_sum
      intro r _
      calc
        _  ≤  ‖l2Diagonal (E r)‖*‖l2ShiftLeft (r.val+1)‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _  ≤  ‖E r‖*1 := mul_le_mul (norm_l2Diagonal_le _) (norm_l2ShiftLeft_le _) (norm_nonneg _) (norm_nonneg _)
        _  ≤  ‖E‖ := by simpa using norm_le_pi_norm E r
    _ = _ := by simp

/-- The bounded ℓ² operator represented by a fixed-band coefficient array. -/
def bandOperator {p q : ℕ} (E : FullBand p q) : L2 →L[ℝ] L2 :=
  lowerBandOperator E.1+l2Diagonal E.2.1+upperBandOperator E.2.2

theorem bandOperator_basis {p q : ℕ} (E : FullBand p q) (i j : ℕ) :
    bandOperator E (l2Basis j) i=fullEntry E i j := by
  simp only [bandOperator,add_apply,lp.coeFn_add,Pi.add_apply,
    lowerBandOperator_basis,upperBandOperator_basis,l2Diagonal_apply,l2Basis_apply]
  unfold fullEntry
  by_cases he : i=j
  · subst j
    simp
  · by_cases hl : j < i
    · simp [he,hl,bandEntry_upper E.2.2 (by omega : j ≤ i)]
    · have hu : i ≤ j := by omega
      simp [he,hl,bandEntry_upper E.1 hu]

theorem norm_bandOperator_le {p q : ℕ} (E : FullBand p q) :
    ‖bandOperator E‖ ≤ (p+q+1:ℝ)*‖E‖ := by
  have h₁ : ‖E.1‖ ≤ ‖E‖ := le_max_left _ _
  have h₂ : ‖E.2.1‖ ≤ ‖E‖ := (le_max_left _ _).trans (le_max_right _ _)
  have h₃ : ‖E.2.2‖ ≤ ‖E‖ := (le_max_right _ _).trans (le_max_right _ _)
  calc
    _  ≤  ‖lowerBandOperator E.1‖+‖l2Diagonal E.2.1‖+‖upperBandOperator E.2.2‖ :=
      (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
    _  ≤  (p:ℝ)*‖E.1‖+‖E.2.1‖+(q:ℝ)*‖E.2.2‖ :=
      add_le_add (add_le_add (norm_lowerBandOperator_le _) (norm_l2Diagonal_le _)) (norm_upperBandOperator_le _)
    _  ≤  (p:ℝ)*‖E‖+‖E‖+(q:ℝ)*‖E‖ := by gcongr
    _ = _ := by ring

theorem fullEntry_le_operatorNorm {p q : ℕ} (E : FullBand p q) (i j : ℕ) :
    |fullEntry E i j| ≤ ‖bandOperator E‖ := by
  rw [←bandOperator_basis]
  calc
    _  ≤  ‖bandOperator E (l2Basis j)‖ := lp.norm_apply_le_norm (by norm_num) _ _
    _  ≤  ‖bandOperator E‖*‖l2Basis j‖ := ContinuousLinearMap.le_opNorm _ _
    _ = _ := by simp

/-- The operator norm controls every coefficient uniformly. -/
theorem coefficientNorm_le_operatorNorm {p q : ℕ} (E : FullBand p q) :
    ‖E‖ ≤ ‖bandOperator E‖ := by
  apply max_le
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro r
    apply BoundedContinuousFunction.norm_le_of_nonempty.mpr
    intro j
    simpa using fullEntry_le_operatorNorm E (j+r.val+1) j
  · apply max_le
    · apply BoundedContinuousFunction.norm_le_of_nonempty.mpr
      intro j
      simpa using fullEntry_le_operatorNorm E j j
    · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
      intro r
      apply BoundedContinuousFunction.norm_le_of_nonempty.mpr
      intro j
      simpa using fullEntry_le_operatorNorm E j (j+r.val+1)

private theorem l2Operator_ext_basis {A B : L2 →L[ℝ] L2}
    (h : ∀ j, A (l2Basis j)=B (l2Basis j)) : A=B := by
  apply lp.ext_continuousLinearMap (by norm_num : (2:ENNReal)≠⊤)
  intro j
  apply ContinuousLinearMap.ext
  intro c
  have he : lp.single 2 j c=(c:ℝ) • l2Basis j := by
    apply lp.ext
    funext n
    simp only [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,l2Basis_apply,lp.single_apply,
      Pi.single_apply]
    split_ifs <;> simp
  change A (lp.single 2 j c)=B (lp.single 2 j c)
  rw [he,map_smul,map_smul,h j]

theorem bandOperator_add {p q : ℕ} (E F : FullBand p q) :
    bandOperator (E+F)=bandOperator E+bandOperator F := by
  apply l2Operator_ext_basis
  intro j
  apply lp.ext
  funext i
  simp only [add_apply,lp.coeFn_add,Pi.add_apply,bandOperator_basis,fullEntry_add]

theorem bandOperator_smul {p q : ℕ} (c : ℝ) (E : FullBand p q) :
    bandOperator (c • E)=c • bandOperator E := by
  apply l2Operator_ext_basis
  intro j
  apply lp.ext
  funext i
  simp only [smul_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,
    bandOperator_basis,fullEntry_smul]

/-- The continuous linear realization of fixed-band matrices as ℓ² operators. -/
def bandOperatorCLM (p q : ℕ) : FullBand p q →L[ℝ] (L2 →L[ℝ] L2) :=
  LinearMap.mkContinuous
    { toFun:=bandOperator
      map_add':=bandOperator_add
      map_smul':=fun c E=>bandOperator_smul c E }
    (p+q+1:ℝ) norm_bandOperator_le

@[simp] theorem bandOperatorCLM_apply (p q : ℕ) (E : FullBand p q) :
    bandOperatorCLM p q E=bandOperator E := rfl

theorem bandOperator_antilipschitz (p q : ℕ) : AntilipschitzWith 1 (bandOperatorCLM p q) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro E F
  simp only [NNReal.coe_one,one_mul,dist_eq_norm]
  rw [←map_sub]
  exact coefficientNorm_le_operatorNorm (E-F)

theorem bandOperator_injective (p q : ℕ) : Function.Injective (bandOperatorCLM p q) :=
  (bandOperator_antilipschitz p q).injective

/-- The finite-band operator space has exactly the topology of the bounded
coefficient space used in the stability proofs. -/
def bandOperatorEquivRange (p q : ℕ) : FullBand p q ≃L[ℝ] (bandOperatorCLM p q).range :=
  (bandOperatorCLM p q).equivRange (bandOperator_injective p q)
    ((bandOperator_antilipschitz p q).isClosed_range (bandOperatorCLM p q).uniformContinuous)

/-- Actual matrix entries of an arbitrary bounded ℓ² operator. -/
def operatorEntry (A : L2 →L[ℝ] L2) (i j : ℕ) : ℝ := A (l2Basis j) i

theorem operatorEntry_bound (A : L2 →L[ℝ] L2) (i j : ℕ) : |operatorEntry A i j|≤‖A‖ := by
  calc
    _ ≤ ‖A (l2Basis j)‖ := lp.norm_apply_le_norm (by norm_num) _ _
    _ ≤ ‖A‖*‖l2Basis j‖ := ContinuousLinearMap.le_opNorm _ _
    _ = _ := by simp

/-- The image is exactly the operators with the prescribed bandwidth,
not a smaller abstract model. -/
theorem bandOperator_range_iff (p q : ℕ) (A : L2 →L[ℝ] L2) :
    A∈(bandOperatorCLM p q).range ↔
      ∀ i j, j+p < i ∨ i+q < j → operatorEntry A i j=0 := by
  constructor
  · rintro ⟨E,rfl⟩ i j h
    change bandOperator E (l2Basis j) i=0
    rw [bandOperator_basis]
    exact fullEntry_band E i j h
  · intro h
    let E : FullBand p q:=fullOfEntries (operatorEntry A) ‖A‖ (operatorEntry_bound A)
    refine ⟨E,?_⟩
    apply l2Operator_ext_basis
    intro j
    apply lp.ext
    funext i
    change bandOperator E (l2Basis j) i=operatorEntry A i j
    rw [bandOperator_basis]
    exact fullOfEntries_entry _ _ _ h i j

#print axioms bandOperator_basis
#print axioms norm_bandOperator_le
#print axioms coefficientNorm_le_operatorNorm
#print axioms bandOperatorEquivRange
#print axioms bandOperator_range_iff

end BTP.GeneralStability
