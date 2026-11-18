import PowerConvexity.Calculus.TracePowerFirstLimit
import PowerConvexity.Analysis.TracePowerSecondNormalization

/-! # Value convergence of the positive trace-root approximation -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
namespace PowerConvexity
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem trace_power_root_factor (k : ι → ℝ) (i : ι)
    (hi : 0 < k i) (h0 : ∀ j, 0 ≤ k j) (n : ℕ) :
    (∑ j, k j^(n+1)) ^ (1/((n:ℝ)+1)) =
      k i * (normalizedTracePower (fun j => k j/k i) (n+1)) ^ (1/((n:ℝ)+1)) := by
  rw [trace_power_sum_factor k i hi.ne' (n+1)]
  have hs : 0 ≤ normalizedTracePower (fun j => k j/k i) (n+1) :=
    Finset.sum_nonneg (fun j _ => pow_nonneg (div_nonneg (h0 j) hi.le) _)
  rw [Real.mul_rpow (pow_nonneg hi.le _) hs, ← Real.rpow_natCast_mul hi.le]
  have he : ((n+1:ℕ):ℝ)*(1/((n:ℝ)+1)) = 1 := by push_cast; field_simp
  rw [he, Real.rpow_one]

theorem trace_power_root_tendsto (k : ι → ℝ) (i : ι)
    (hi : 0 < k i) (h0 : ∀ j, 0 ≤ k j) (hgap : ∀ j, j ≠ i → k j < k i) :
    Filter.Tendsto (fun n : ℕ => (∑ j, k j^(n+1)) ^ (1/((n:ℝ)+1)))
      Filter.atTop (𝓝 (k i)) := by
  have hS := normalizedTracePower_tendsto (fun j => k j/k i) i (div_self hi.ne')
    (fun j => div_nonneg (h0 j) hi.le) (fun j hj => (div_lt_one hi).mpr (hgap j hj))
  have hR := hS.rpow (tendsto_one_div_add_atTop_nhds_zero_nat :
    Filter.Tendsto (fun n : ℕ => 1/((n:ℝ)+1)) Filter.atTop (𝓝 0)) (Or.inl one_ne_zero)
  simp_rw [trace_power_root_factor k i hi h0]
  convert hR.const_mul (k i) using 1 <;> first | rfl | simp

variable {E : Type*}

theorem tracePowerRoot_value_tendsto {K : E → Matrix ι ι ℂ} (x : E)
    (k : ι → ℝ) (i : ι) (hdiag : K x = Matrix.diagonal (fun j => (k j:ℂ)))
    (hi : 0 < k i) (h0 : ∀ j, 0 ≤ k j) (hgap : ∀ j, j ≠ i → k j < k i) :
    Filter.Tendsto (fun n : ℕ => tracePowerRoot K (n+1) x) Filter.atTop (𝓝 (k i)) := by
  simp only [tracePowerRoot, hdiag, real_diagonal_trace_power, Complex.ofReal_re,
    Nat.cast_add, Nat.cast_one]
  exact trace_power_root_tendsto k i hi h0 hgap

end PowerConvexity
