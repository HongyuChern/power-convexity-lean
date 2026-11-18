import PowerConvexity.Analysis.TracePowerSecondContraction

/-! # Exact normalization of both terms in the B4 cancellation -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
namespace PowerConvexity
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem trace_power_sum_factor (k : ι → ℝ) (i : ι) (hi : k i ≠ 0) (p : ℕ) :
    (∑ j, k j^p) = k i^p * normalizedTracePower (fun j => k j/k i) p := by
  have hp : k i^p ≠ 0 := pow_ne_zero _ hi
  simp only [normalizedTracePower, div_pow, ← Finset.sum_div]
  field_simp

theorem trace_power_second_denominator_factor (k : ι → ℝ) (i : ι)
    (hi : 0 < k i) (h0 : ∀ j, 0 ≤ k j) (n : ℕ) :
    (∑ j, k j^(n+2)) ^ ((2*((n:ℝ)+2)-1)/((n:ℝ)+2)) =
      k i^(n+1)*k i^(n+1)*k i * traceRootSecondWeight (fun j => k j/k i) n := by
  have hT : 0 < ∑ j, k j^(n+2) := Finset.sum_pos' (fun j _ => pow_nonneg (h0 j) _)
    ⟨i, Finset.mem_univ i, pow_pos hi _⟩
  have he : (2*((n:ℝ)+2)-1)/((n:ℝ)+2) = ((n:ℝ)+1)/((n:ℝ)+2)+1 := by
    field_simp; ring
  rw [he, Real.rpow_add_one hT.ne']
  have hD := trace_power_denominator_factor k i hi h0 (n+1)
  simp only [Nat.cast_add, Nat.cast_one, add_assoc] at hD
  norm_num at hD
  rw [hD, trace_power_sum_factor k i hi.ne' (n+2)]
  change k i^(n+1) * traceRootWeight (fun j => k j/k i) n *
    (k i^(n+2)*normalizedTracePower (fun j => k j/k i) (n+2)) = _
  rw [show n+2=(n+1)+1 by omega, pow_succ]
  unfold traceRootSecondWeight
  ring

theorem trace_power_convolution_factor (k : ι → ℝ) (i : ι) (hi : k i ≠ 0)
    (l m : ι) (n : ℕ) :
    (∑ j ∈ Finset.range (n+1), k l^j*k m^(n-j)) =
      k i^n * (∑ j ∈ Finset.range (n+1), (k l/k i)^j*(k m/k i)^(n-j)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have he : k i^n = k i^j*k i^(n-j) := by rw [← pow_add, Nat.add_sub_of_le hjn]
  rw [he, div_pow, div_pow]
  field_simp

theorem trace_power_convolution_coefficient_normalize (k : ι → ℝ) (i : ι)
    (hi : 0 < k i) (h0 : ∀ j, 0 ≤ k j) (l m : ι) (n : ℕ) :
    (∑ j ∈ Finset.range (n+1), k l^j*k m^(n-j)) /
        (∑ j, k j^(n+2)) ^ (((n:ℝ)+1)/((n:ℝ)+2)) =
      (k i)⁻¹ * ((∑ j ∈ Finset.range (n+1), (k l/k i)^j*(k m/k i)^(n-j)) /
        traceRootWeight (fun j => k j/k i) n) := by
  have hD := trace_power_denominator_factor k i hi h0 (n+1)
  simp only [Nat.cast_add, Nat.cast_one, add_assoc] at hD
  norm_num at hD
  rw [hD, trace_power_convolution_factor k i hi.ne' l m n]
  change k i^n * _ / (k i^(n+1)*traceRootWeight (fun j => k j/k i) n) = _
  have hW : traceRootWeight (fun j => k j/k i) n ≠ 0 := ne_of_gt
    (traceRootWeight_pos (fun j => k j/k i) i (div_self hi.ne') (fun j => div_nonneg (h0 j) hi.le) n)
  rw [pow_succ]
  field_simp

theorem trace_power_rank_coefficient_normalize (k : ι → ℝ) (i : ι)
    (hi : 0 < k i) (h0 : ∀ j, 0 ≤ k j) (l m : ι) (n : ℕ) :
    ((n:ℝ)+1)*k l^(n+1)*k m^(n+1) /
        (∑ j, k j^(n+2)) ^ ((2*((n:ℝ)+2)-1)/((n:ℝ)+2)) =
      (k i)⁻¹ * ((((n:ℝ)+1)*(k l/k i)^(n+1)*(k m/k i)^(n+1)) /
        traceRootSecondWeight (fun j => k j/k i) n) := by
  rw [trace_power_second_denominator_factor k i hi h0 n]
  set V := traceRootSecondWeight (fun j => k j/k i) n
  simp only [div_pow, div_eq_mul_inv, mul_inv_rev]
  ring

end PowerConvexity
