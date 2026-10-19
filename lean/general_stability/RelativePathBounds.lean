import RelativeExtraction

/-! Positive coefficient estimates for the relative extraction inverse.
Every comparison uses factor entries at exactly the same row. -/

noncomputable section
namespace BTP.RelativeStability
open Finset BTP.GeneralStability

/-- The contribution of the last s factors, an actual positive path. -/
def lastPath (c : ℕ → ℕ → ℝ) (m s n : ℕ) : ℝ :=
  ∏ t ∈ range s, c (m-s+t) (n-t)

@[simp] theorem lastPath_zero (c : ℕ → ℕ → ℝ) (m n : ℕ) : lastPath c m 0 n=1 := by
  simp [lastPath]

theorem lastPath_nonneg (c : ℕ → ℕ → ℝ) (hc : ∀ i n, 0≤c i n)
    (m s n : ℕ) : 0≤lastPath c m s n :=
  prod_nonneg (fun _ _=>hc _ _)

theorem lastPath_pos (c : ℕ → ℕ → ℝ) (hc : ∀ i n, 0<c i n)
    (m s n : ℕ) : 0<lastPath c m s n :=
  prod_pos (fun _ _=>hc _ _)

theorem lastPath_succ_right (c : ℕ → ℕ → ℝ) (m s n : ℕ) (hs : s<m) :
    lastPath c m (s+1) n = lastPath c (m-1) s n * c (m-1) (n-s) := by
  unfold lastPath
  rw [prod_range_succ]
  have hsub : m-(s+1) = m-1-s := by omega
  rw [hsub, show m-1-s+s=m-1 by omega]

theorem lastPath_succ_left (c : ℕ → ℕ → ℝ) (m s n : ℕ) (hs : s<m) :
    lastPath c m (s+1) n = c (m-s-1) n * lastPath c m s (n-1) := by
  unfold lastPath
  rw [prod_range_succ']
  simp only [Nat.add_zero, Nat.sub_zero]
  have he : (fun t=>c (m-(s+1)+(t+1)) (n-(t+1))) =
      fun t=>c (m-s+t) (n-1-t) := by
    funext t
    congr 1 <;> omega
  rw [he, show m-(s+1)=m-s-1 by omega]
  ring

theorem productCoefficients_nonneg (c : ℕ → ℕ → ℝ)
    (hc : ∀ i n, 0≤c i n) (k s n : ℕ) : 0≤productCoefficients c k s n := by
  induction k generalizing s n with
  | zero => cases s <;> simp [productCoefficients]
  | succ k ih =>
    cases s with
    | zero => simp [productCoefficients_diagonal]
    | succ s =>
      change 0≤productCoefficients c k (s+1) n + productCoefficients c k s n*c k (n-s)
      exact add_nonneg (ih _ _) (mul_nonneg (ih _ _) (hc _ _))

/-- A uniform bound using the last-s path; the factor 2^k bounds the
number of paths, while K compares factor indices at the same row. -/
theorem productCoefficients_le_lastPath (c : ℕ → ℕ → ℝ)
    (hc : ∀ i n, 0≤c i n) (K : ℝ) (hK : 1≤K)
    (hcomp : ∀ i j n, i≤j → c i n≤K*c j n)
    (k m s n : ℕ) (hkm : k≤m) (hsm : s≤m) :
    productCoefficients c k s n ≤ (2:ℝ)^k*K^s*lastPath c m s n := by
  induction k generalizing m s n with
  | zero =>
    cases s with
    | zero => simp [productCoefficients]
    | succ s =>
      simp only [productCoefficients, pow_zero, one_mul]
      exact mul_nonneg (pow_nonneg (by linarith) _) (lastPath_nonneg c hc _ _ _)
  | succ k ih =>
    cases s with
    | zero =>
      simp only [productCoefficients_diagonal, pow_zero, mul_one, lastPath_zero]
      exact one_le_pow₀ (by norm_num)
    | succ s =>
      have hs : s<m := by omega
      change productCoefficients c k (s+1) n + productCoefficients c k s n*c k (n-s) ≤ _
      have hfirst := ih m (s+1) n (by omega) hsm
      have hsecond := ih (m-1) s n (by omega) (by omega)
      have hfactor := hcomp k (m-1) (n-s) (by omega)
      have hbound := mul_le_mul hsecond hfactor (hc _ _)
        (mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg (by linarith) _))
          (lastPath_nonneg c hc _ _ _))
      rw [lastPath_succ_right c m s n hs] at hfirst ⊢
      calc
        _ ≤ (2:ℝ)^k*K^(s+1)*(lastPath c (m-1) s n*c (m-1) (n-s)) +
            ((2:ℝ)^k*K^s*lastPath c (m-1) s n)*(K*c (m-1) (n-s)) := add_le_add hfirst hbound
        _ = _ := by rw [pow_succ, pow_succ]; ring

/-- The same path is present with coefficient one in the true product. -/
theorem lastPath_le_productCoefficients (c : ℕ → ℕ → ℝ)
    (hc : ∀ i n, 0≤c i n) (k s n : ℕ) (hs : s≤k) :
    lastPath c k s n ≤ productCoefficients c k s n := by
  induction k generalizing s n with
  | zero =>
    have : s=0 := by omega
    subst s
    simp [productCoefficients]
  | succ k ih =>
    cases s with
    | zero => simp [productCoefficients_diagonal]
    | succ s =>
      rw [lastPath_succ_right c (k+1) s n (by omega)]
      simp only [Nat.add_sub_cancel]
      change lastPath c k s n*c k (n-s) ≤
        productCoefficients c k (s+1) n+productCoefficients c k s n*c k (n-s)
      exact (mul_le_mul_of_nonneg_right (ih s n (by omega)) (hc _ _)).trans
        (le_add_of_nonneg_left (productCoefficients_nonneg c hc _ _ _))

/-- Left multiplication by the first subdiagonal respects the same path
scale. This controls every repeated first factor in elimination. -/
theorem head_mul_lastPath_le (c : ℕ → ℕ → ℝ)
    (hc : ∀ i n, 0≤c i n) (K : ℝ)
    (hcomp : ∀ i j n, i≤j → c i n≤K*c j n)
    (m s n : ℕ) (hs : s<m) :
    c 0 n*lastPath c m s (n-1) ≤ K*lastPath c m (s+1) n := by
  rw [lastPath_succ_left c m s n hs]
  have hh := mul_le_mul_of_nonneg_right (hcomp 0 (m-s-1) n (Nat.zero_le _))
    (lastPath_nonneg c hc m s (n-1))
  simpa only [mul_assoc] using hh

/-- Finite elimination is bounded relative to the corresponding last
path. The bound is independent of the row index. -/
theorem eliminate_le_lastPath (c : ℕ → ℕ → ℝ)
    (hc : ∀ i n, 0≤c i n) (K : ℝ) (hK : 1≤K)
    (hcomp : ∀ i j n, i≤j → c i n≤K*c j n)
    (m : ℕ) (E : RowCoefficients) (B : ℝ) (hB : 0≤B)
    (hE : ∀ s n, s≤m → |E s n|≤B*K^s*lastPath c m s n)
    (s n : ℕ) (hs : s≤m) :
    |eliminate (c 0) E s n|≤(s:ℝ)*B*K^s*lastPath c m s n := by
  induction s generalizing n with
  | zero => simp [eliminate]
  | succ s ih =>
    have hh := ih (n-1) (by omega)
    have hp := head_mul_lastPath_le c hc K hcomp m s n (by omega)
    have hmul := mul_le_mul_of_nonneg_left hh (hc 0 n)
    have hconst : 0≤(s:ℝ)*B*K^s := by positivity
    calc
      |eliminate (c 0) E (s+1) n| = |E (s+1) n-c 0 n*eliminate (c 0) E s (n-1)| := rfl
      _ ≤ |E (s+1) n|+|c 0 n*eliminate (c 0) E s (n-1)| := abs_sub _ _
      _ = |E (s+1) n|+c 0 n*|eliminate (c 0) E s (n-1)| := by rw [abs_mul, abs_of_nonneg (hc 0 n)]
      _ ≤ B*K^(s+1)*lastPath c m (s+1) n+c 0 n*((s:ℝ)*B*K^s*lastPath c m s (n-1)) :=
        add_le_add (hE _ _ hs) hmul
      _ = B*K^(s+1)*lastPath c m (s+1) n+((s:ℝ)*B*K^s)*(c 0 n*lastPath c m s (n-1)) := by ring
      _ ≤ B*K^(s+1)*lastPath c m (s+1) n+((s:ℝ)*B*K^s)*(K*lastPath c m (s+1) n) :=
        add_le_add_right (mul_le_mul_of_nonneg_left hp hconst) _
      _ = _ := by rw [Nat.cast_add, Nat.cast_one, pow_succ]; ring

theorem lastPath_all_eq_scale (c : ℕ → ℕ → ℝ) (k n : ℕ) :
    lastPath c (k+1) (k+1) n = scale c k n := by
  unfold lastPath scale
  simp only [Nat.sub_self, Nat.zero_add]
  rw [prod_range_succ']
  have he : (fun t=>c (t+1) (n-(t+1))) = fun t=>c (t+1) (n-t-1) := by
    funext t
    rw [show n-(t+1)=n-t-1 by omega]
  rw [he]
  simp only [Nat.sub_zero]
  ring

theorem lastPath_tail (c : ℕ → ℕ → ℝ) (m s n : ℕ) (hs : s≤m) :
    lastPath (fun i=>c (i+1)) m s n = lastPath c (m+1) s n := by
  unfold lastPath
  apply prod_congr rfl
  intro t _
  change c (m-s+t+1) (n-t)=_
  rw [show m-s+t+1=m+1-s+t by omega]

/-- Uniform relative forcing estimate, with the same deepest entry as
used to normalize the scalar recurrence. -/
theorem relative_forcing_bound (c : ℕ → ℕ → ℝ)
    (hc : ∀ i n, 0≤c i n) (K : ℝ) (hK : 1≤K)
    (hcomp : ∀ i j n, i≤j → c i n≤K*c j n)
    (m : ℕ) (E : RowCoefficients) (M : ℝ) (hM : 0≤M)
    (hE : ∀ s n, s≤m → |E s n|≤M*productCoefficients c m s n)
    (s n : ℕ) (hs : s≤m) :
    |eliminate (c 0) E s n|≤(s:ℝ)*(M*2^m)*K^s*lastPath c m s n := by
  apply eliminate_le_lastPath c hc K hK hcomp m E (M*2^m) (by positivity)
  · intro t row ht
    calc
      |E t row| ≤ M*productCoefficients c m t row := hE t row ht
      _ ≤ M*((2:ℝ)^m*K^t*lastPath c m t row) :=
        mul_le_mul_of_nonneg_left (productCoefficients_le_lastPath c hc K hK hcomp m m t row (le_refl _) ht) hM
      _ = _ := by ring
  · exact hs

theorem head_variation_le_lastPath (c : ℕ → ℕ → ℝ)
    (hc : ∀ i n, 0≤c i n) (K : ℝ) (hK : 1≤K)
    (hcomp : ∀ i j n, i≤j → c i n≤K*c j n)
    (m : ℕ) (hm : 0<m) (h : ℕ → ℝ) (H : ℝ) (hH : 0≤H)
    (hh : ∀ n, |h n|≤H*c 0 n) (s n : ℕ) (hs : s≤m) :
    |leftVariation h (productCoefficients (fun i=>c (i+1)) (m-1)) s n| ≤
      (H*2^(m-1))*K^s*lastPath c m s n := by
  cases s with
  | zero =>
    simp only [leftVariation, abs_zero, pow_zero, mul_one, lastPath_zero]
    positivity
  | succ s =>
    have hg := productCoefficients_le_lastPath (fun i=>c (i+1)) (fun i n=>hc (i+1) n)
      K hK (fun i j n hij=>hcomp (i+1) (j+1) n (by omega)) (m-1) (m-1) s (n-1)
      (le_refl _) (by omega)
    rw [lastPath_tail c (m-1) s (n-1) (by omega), show m-1+1=m by omega] at hg
    have hp := head_mul_lastPath_le c hc K hcomp m s n (by omega)
    calc
      _ = |h n| * productCoefficients (fun i=>c (i+1)) (m-1) s (n-1) := by
        rw [leftVariation, abs_mul, abs_of_nonneg (productCoefficients_nonneg _ (fun i n=>hc (i+1) n) _ _ _)]
      _ ≤ (H*c 0 n)*((2:ℝ)^(m-1)*K^s*lastPath c m s (n-1)) :=
        mul_le_mul (hh n) hg (productCoefficients_nonneg _ (fun i n=>hc (i+1) n) _ _ _)
          (mul_nonneg hH (hc 0 n))
      _ = (H*2^(m-1)*K^s)*(c 0 n*lastPath c m s (n-1)) := by ring
      _ ≤ (H*2^(m-1)*K^s)*(K*lastPath c m (s+1) n) :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      _ = _ := by rw [pow_succ]; ring

def extractionBound (m : ℕ) (K : ℝ) : ℝ := (m:ℝ)*2^m*K^m

theorem relative_remainder_bound (c : ℕ → ℕ → ℝ)
    (hc : ∀ i n, 0≤c i n) (K : ℝ) (hK : 1≤K)
    (hcomp : ∀ i j n, i≤j → c i n≤K*c j n)
    (m : ℕ) (hm : 0<m) (E : RowCoefficients) (M : ℝ) (hM : 0≤M)
    (hE : ∀ s n, s≤m → |E s n|≤M*productCoefficients c m s n)
    (h : ℕ → ℝ) (H : ℝ) (hH : 0≤H) (hh : ∀ n, |h n|≤H*c 0 n)
    (s n : ℕ) (hs : s<m) :
    |eliminate (c 0) E s n - eliminate (c 0)
        (leftVariation h (productCoefficients (fun i=>c (i+1)) (m-1))) s n| ≤
      extractionBound m K*(M+H)*productCoefficients (fun i=>c (i+1)) (m-1) s n := by
  have he := relative_forcing_bound c hc K hK hcomp m E M hM hE s n (by omega)
  have hhg := eliminate_le_lastPath c hc K hK hcomp m
    (leftVariation h (productCoefficients (fun i=>c (i+1)) (m-1))) (H*2^(m-1))
    (by positivity) (head_variation_le_lastPath c hc K hK hcomp m hm h H hH hh) s n (by omega)
  have hp := lastPath_le_productCoefficients (fun i=>c (i+1)) (fun i n=>hc (i+1) n)
    (m-1) s n (by omega)
  rw [lastPath_tail c (m-1) s n (by omega), show m-1+1=m by omega] at hp
  have hpow : (2:ℝ)^(m-1)≤2^m := pow_le_pow_right₀ (by norm_num) (Nat.sub_le m 1)
  have hkpow : K^s≤K^m := pow_le_pow_right₀ hK hs.le
  have hsm : (s:ℝ)≤m := by exact_mod_cast hs.le
  have hscale : (s:ℝ)*K^s≤(m:ℝ)*K^m := mul_le_mul hsm hkpow (pow_nonneg (by linarith) _) (by positivity)
  calc
    _ ≤ |eliminate (c 0) E s n| + |eliminate (c 0)
        (leftVariation h (productCoefficients (fun i=>c (i+1)) (m-1))) s n| := abs_sub _ _
    _ ≤ (s:ℝ)*(M*2^m)*K^s*lastPath c m s n +
        (s:ℝ)*(H*2^(m-1))*K^s*lastPath c m s n := add_le_add he hhg
    _ = ((s:ℝ)*K^s)*(M*2^m+H*2^(m-1))*lastPath c m s n := by ring
    _ ≤ ((m:ℝ)*K^m)*(M*2^m+H*2^m)*productCoefficients (fun i=>c (i+1)) (m-1) s n := by
      apply mul_le_mul
      · exact mul_le_mul hscale (add_le_add_right (mul_le_mul_of_nonneg_left hpow hH) _)
          (by positivity) (by positivity)
      · exact hp
      · exact lastPath_nonneg c hc _ _ _
      · positivity
    _ = _ := by unfold extractionBound; ring

#print axioms relative_forcing_bound
#print axioms relative_remainder_bound
#print axioms productCoefficients_le_lastPath
#print axioms lastPath_le_productCoefficients
#print axioms eliminate_le_lastPath
end BTP.RelativeStability
