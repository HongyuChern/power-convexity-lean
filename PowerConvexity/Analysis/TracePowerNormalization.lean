import PowerConvexity.Analysis.TracePowerLimits

/-! # Exact removal of the dominant eigenvalue from Appendix B denominators -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace PowerConvexity
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem trace_power_denominator_factor (k : ι → ℝ) (i : ι)
    (hi : 0 < k i) (h0 : ∀ j, 0 ≤ k j) (n : ℕ) :
    (∑ j, k j^(n+1)) ^ ((n:ℝ)/(n+1)) =
      k i^n * (normalizedTracePower (fun j => k j/k i) (n+1)) ^ ((n:ℝ)/(n+1)) := by
  have hpow : k i^(n+1) ≠ 0 := pow_ne_zero _ hi.ne'
  have hf : (∑ j, k j^(n+1)) =
      k i^(n+1) * normalizedTracePower (fun j => k j/k i) (n+1) := by
    simp only [normalizedTracePower, div_pow, ← Finset.sum_div]
    field_simp
  have hs : 0 ≤ normalizedTracePower (fun j => k j/k i) (n+1) :=
    Finset.sum_nonneg (fun j _ => pow_nonneg (div_nonneg (h0 j) hi.le) _)
  rw [hf, Real.mul_rpow (pow_nonneg hi.le _) hs, ← Real.rpow_natCast_mul hi.le]
  have he : ((n+1:ℕ):ℝ) * ((n:ℝ)/(n+1)) = (n:ℝ) := by
    push_cast
    field_simp
  rw [he, Real.rpow_natCast]

theorem trace_power_first_contraction_normalize (k : ι → ℝ) (i : ι)
    (hi : 0 < k i) (h0 : ∀ j, 0 ≤ k j) (X : ι → ℂ) (n : ℕ) :
    (∑ j, (k j:ℂ)^n * X j) / (((∑ j, k j^(n+1)) ^ ((n:ℝ)/(n+1)) : ℝ):ℂ) =
      ∑ j, (((k j/k i)^n /
        (normalizedTracePower (fun t => k t/k i) (n+1)) ^ ((n:ℝ)/(n+1)) : ℝ):ℂ) * X j := by
  rw [trace_power_denominator_factor k i hi h0 n, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  set W : ℝ := (normalizedTracePower (fun t => k t/k i) (n+1)) ^ ((n:ℝ)/(n+1))
  simp only [div_pow, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_mul,
    div_eq_mul_inv, mul_inv_rev, Complex.ofReal_inv]
  ring

theorem trace_power_first_contraction_limit (k : ι → ℝ) (i : ι)
    (hi : 0 < k i) (h0 : ∀ j, 0 ≤ k j) (hgap : ∀ j, j ≠ i → k j < k i)
    (X : ι → ℂ) :
    Filter.Tendsto (fun n : ℕ => (∑ j, (k j:ℂ)^n * X j) /
      (((∑ j, k j^(n+1)) ^ ((n:ℝ)/(n+1)) : ℝ):ℂ))
      Filter.atTop (nhds (X i)) := by
  simp_rw [trace_power_first_contraction_normalize k i hi h0 X]
  exact normalizedTracePower_first_contraction_tendsto (fun j => k j/k i) i
    (div_self hi.ne') (fun j => div_nonneg (h0 j) hi.le)
    (fun j hj => (div_lt_one hi).mpr (hgap j hj)) X

end PowerConvexity
