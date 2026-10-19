import LowerGeneralCriterion

/-! Algebraic normalization of relative extraction equations. No
boundedness is assumed on the original factor entries. -/

noncomputable section
open Finset
namespace BTP.RelativeStability

def scale (c : ℕ → ℕ → ℝ) (j n : ℕ) : ℝ :=
  c 0 n * ∏ l ∈ range j, c (l+1) (n-l-1)

def theta (c : ℕ → ℕ → ℝ) (j n : ℕ) : ℝ :=
  ∏ l ∈ range (j+1), c l (n-l-1) / c (l+1) (n-l-1)

theorem scale_pos (c : ℕ → ℕ → ℝ) (hc : ∀ i n, 0<c i n) (j n : ℕ) :
    0<scale c j n := by
  exact mul_pos (hc 0 n) (prod_pos (fun i _ => hc (i+1) (n-i-1)))

theorem scale_succ (c : ℕ → ℕ → ℝ) (j n : ℕ) :
    scale c (j+1) n = scale c j n * c (j+1) (n-j-1) := by
  simp only [scale, prod_range_succ, mul_assoc]

theorem scale_ratio (c : ℕ → ℕ → ℝ) (hc : ∀ i n, 0<c i n) (j n : ℕ) :
    c 0 n * scale c j (n-1) / scale c (j+1) n = theta c j n := by
  induction j with
  | zero =>
    simp only [scale, theta, Nat.zero_add, prod_range_zero, mul_one,
      prod_range_one, Nat.sub_zero]
    have h0 : c 0 n≠0 := ne_of_gt (hc 0 n)
    have h1 : c 1 (n-1)≠0 := ne_of_gt (hc 1 (n-1))
    field_simp
  | succ j ih =>
    rw [scale_succ c (j+1), scale_succ c j (n-1)]
    have hn : n-1-j-1 = n-(j+1)-1 := by omega
    rw [hn]
    have hz : scale c (j+1) n≠0 := ne_of_gt (scale_pos c hc _ _)
    have hz' : c (j+1+1) (n-(j+1)-1)≠0 := ne_of_gt (hc _ _)
    have he : c 0 n * (scale c j (n-1)*c (j+1) (n-(j+1)-1)) /
        (scale c (j+1) n*c (j+1+1) (n-(j+1)-1)) =
        (c 0 n*scale c j (n-1)/scale c (j+1) n)*
        (c (j+1) (n-(j+1)-1)/c (j+1+1) (n-(j+1)-1)) := by ring
    rw [he, ih]
    simp only [theta, prod_range_succ]

theorem normalized_first_order (c : ℕ → ℕ → ℝ) (hc : ∀ i n, 0<c i n)
    (u : ℕ → ℝ) (j n : ℕ) :
    (c (j+1) (n-j-1) * (scale c j n * u n) -
       c 0 n * (scale c j (n-1)*u (n-1))) / scale c (j+1) n =
      u n - theta c j n*u (n-1) := by
  rw [←scale_ratio c hc j n]
  have hs := scale_succ c j n
  have hz : scale c (j+1) n≠0 := ne_of_gt (scale_pos c hc _ _)
  field_simp
  rw [hs]
  ring

open BTP.GeneralStability

theorem geometric_product (f : ℕ → ℕ → ℝ) (j : ℕ)
    (hf : ∀ l n, 0≤f l n) (hg : ∀ l≤j, GeometricDecay (f l)) :
    GeometricDecay (fun n => ∏ l ∈ range (j+1), f l n) := by
  induction j with
  | zero => simpa using hg 0 (le_refl 0)
  | succ j ih =>
    have hh := ih (fun l hl => hg l (by omega))
    have hn : ∀ n, 0≤∏ l ∈ range (j+1), f l n :=
      fun n => prod_nonneg (fun l _ => hf l n)
    have ht := GeometricDecay.mul hn (hf (j+1)) hh (hg (j+1) (le_refl _))
    simpa only [prod_range_succ] using ht

theorem theta_geometric (c : ℕ → ℕ → ℝ) (hc : ∀ i n, 0<c i n) (j : ℕ)
    (hg : ∀ l≤j, GeometricDecay (fun n => c l n/c (l+1) n)) :
    GeometricDecay (fun n => theta c j (n+j+2)) := by
  let f : ℕ → ℕ → ℝ := fun l n => c l (n+(j+1-l))/c (l+1) (n+(j+1-l))
  have hf : ∀ l n, 0≤f l n := fun l n => div_nonneg (hc _ _).le (hc _ _).le
  have hgf : ∀ l≤j, GeometricDecay (f l) := by
    intro l hl
    have hh := (GeometricDecay.shift_iff
      (fun n => div_nonneg (hc l n).le (hc (l+1) n).le) (j+1-l)).mpr (hg l hl)
    simpa [f, Nat.add_comm] using hh
  have he : (fun n => theta c j (n+j+2)) =
      fun n => ∏ l ∈ range (j+1), f l n := by
    funext n
    unfold theta
    apply prod_congr rfl
    intro l hl
    have hl' : l<j+1 := mem_range.mp hl
    dsimp [f]
    have hn : n+j+2-l-1 = n+(j+1-l) := by omega
    rw [hn]
  rw [he]
  exact geometric_product f j hf hgf

/-- The t-th selected index cannot exceed the t-th index of the last
s factors. This is the finite combinatorial fact used in the relative
forcing and remainder estimates. -/
theorem path_index_bound (f : ℕ → ℕ) (m s : ℕ) (hsm : s≤m)
    (hf : ∀ t, t<s → f t<m)
    (hinc : ∀ t, t+1<s → f t<f (t+1))
    (t : ℕ) (ht : t<s) : f t≤m-s+t := by
  have hspan (k : ℕ) (hk : t+k<s) : f t+k≤f (t+k) := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hi := ih (by omega)
      have hs' := hinc (t+k) (by omega)
      have he : t+(k+1)=(t+k)+1 := by omega
      rw [he]
      omega
  have ha := hspan (s-1-t) (by omega)
  have hb := hf (t+(s-1-t)) (by omega)
  omega

theorem path_product_bound (c : ℕ → ℕ → ℝ) (hc : ∀ i n, 0≤c i n)
    (m s n : ℕ) (f : ℕ → ℕ) {K : ℝ}
    (hindex : ∀ t<s, f t≤m-s+t)
    (hcompare : ∀ i j t, i≤j → c i t≤K*c j t) :
    (∏ t ∈ range s, c (f t) (n-t)) ≤
      K^s*∏ t ∈ range s, c (m-s+t) (n-t) := by
  calc
    _ ≤ ∏ t ∈ range s, K*c (m-s+t) (n-t) := by
      exact prod_le_prod (fun t _ => hc _ _)
        (fun t ht => hcompare _ _ _ (hindex t (mem_range.mp ht)))
    _ = _ := by simp [prod_mul_distrib]

#print axioms normalized_first_order
#print axioms theta_geometric
#print axioms path_index_bound

end BTP.RelativeStability
