import AnalyticRadius

-- A positive-radius instance with genuine infinite-dimensional data is not
-- required to establish consistency: the scalar identity already witnesses
-- that the hypotheses do not force False or an empty perturbation domain.
example (e : ℝ) (he : ‖e‖ ≤ (1/16 : ℝ)) :
    ∃! h : ℝ, ‖h‖ ≤ (1/8 : ℝ) ∧ h = e := by
  have h := PBFStability.quantitative_radius
    (ContinuousLinearEquiv.refl ℝ ℝ) (fun _ : ℝ => (0 : ℝ))
    (M := 1) (C := 1) (r := 1/8) (e := e)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro y; simp)
    (by intro h hh; norm_num)
    (by intro h hh k hk; simp only [sub_self, norm_zero]; positivity)
    (by norm_num at *; exact he)
  simpa using h
