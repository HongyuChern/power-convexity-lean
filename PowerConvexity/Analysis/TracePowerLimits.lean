import PowerConvexity.Algebra.DiagonalTracePowers
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! # Valid scalar limits for the trace-power approximation in Appendix B

The selected positive eigenvalue has been divided out. Positivity and the
strict gap are explicit; none of these lemmas assumes a derivative limit.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
open Filter
namespace PowerConvexity
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def normalizedTracePower (r : ι → ℝ) (p : ℕ) : ℝ := ∑ j, r j^p

theorem normalizedTracePower_tendsto (r : ι → ℝ) (i : ι) (hi : r i = 1)
    (h0 : ∀ j, 0 ≤ r j) (hgap : ∀ j, j ≠ i → r j < 1) :
    Tendsto (fun n : ℕ => normalizedTracePower r (n+1)) atTop (𝓝 1) := by
  have ht (j : ι) : Tendsto (fun n : ℕ => r j^(n+1)) atTop
      (𝓝 (if j=i then 1 else 0)) := by
    by_cases hj : j=i
    · subst j; simpa [hi] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1))
    · simpa [hj, pow_succ] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one (h0 j) (hgap j hj)).mul_const (r j)
  simpa [normalizedTracePower] using tendsto_finset_sum Finset.univ (fun j _ => ht j)

theorem normalizedTracePower_ge_one (r : ι → ℝ) (i : ι) (hi : r i = 1)
    (h0 : ∀ j, 0 ≤ r j) (p : ℕ) : 1 ≤ normalizedTracePower r p := by
  have h := Finset.single_le_sum (f := fun j => r j^p)
    (fun j _ => pow_nonneg (h0 j) p) (Finset.mem_univ i)
  simpa [normalizedTracePower, hi] using h

theorem normalizedTracePower_weight_tendsto (r : ι → ℝ) (i : ι) (hi : r i = 1)
    (h0 : ∀ j, 0 ≤ r j) (hgap : ∀ j, j ≠ i → r j < 1) :
    Tendsto (fun n : ℕ => (normalizedTracePower r (n+1)) ^
      ((n : ℝ) / (n+1))) atTop (𝓝 1) := by
  simpa using (normalizedTracePower_tendsto r i hi h0 hgap).rpow
    (tendsto_natCast_div_add_atTop (1:ℝ)) (Or.inl one_ne_zero)

theorem normalizedTracePower_first_coefficient_tendsto (r : ι → ℝ) (i : ι) (hi : r i = 1)
    (h0 : ∀ j, 0 ≤ r j) (hgap : ∀ j, j ≠ i → r j < 1) (j : ι) :
    Tendsto (fun n : ℕ => r j^n / ((normalizedTracePower r (n+1)) ^
      ((n : ℝ) / (n+1)))) atTop (𝓝 (if j=i then 1 else 0)) := by
  have ht : Tendsto (fun n : ℕ => r j^n) atTop (𝓝 (if j=i then 1 else 0)) := by
    by_cases hj : j=i
    · subst j; simpa [hi] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1))
    · simpa [hj] using tendsto_pow_atTop_nhds_zero_of_lt_one (h0 j) (hgap j hj)
  convert ht.div (normalizedTracePower_weight_tendsto r i hi h0 hgap) one_ne_zero using 1 <;>
    first | rfl | simp

theorem normalizedTracePower_first_contraction_tendsto (r : ι → ℝ) (i : ι) (hi : r i = 1)
    (h0 : ∀ j, 0 ≤ r j) (hgap : ∀ j, j ≠ i → r j < 1) (X : ι → ℂ) :
    Tendsto (fun n : ℕ => ∑ j,
      (r j^n / ((normalizedTracePower r (n+1)) ^ ((n : ℝ) / (n+1))) : ℝ) * X j)
      atTop (𝓝 (X i)) := by
  have ht (j : ι) := (Complex.continuous_ofReal.continuousAt.tendsto.comp
    (normalizedTracePower_first_coefficient_tendsto r i hi h0 hgap j)).mul_const (X j)
  simpa only [apply_ite Complex.ofReal, Complex.ofReal_one, Complex.ofReal_zero,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, Function.comp_def]
    using tendsto_finsetSum Finset.univ (fun j _ => ht j)

theorem divided_power_sum_tendsto_zero {a b : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hb0 : 0 ≤ b) (hb1 : b < 1) :
    Tendsto (fun n : ℕ => ∑ j ∈ Finset.range (n+1), a^j * b^(n-j)) atTop (𝓝 0) := by
  by_cases hab : a=b
  · subst b
    have he (n : ℕ) : (∑ j ∈ Finset.range (n+1), a^j * a^(n-j)) = ((n:ℝ)+1)*a^n := by
      have hp (j : ℕ) (hj : j ∈ Finset.range (n+1)) : a^j*a^(n-j)=a^n := by
        rw [← pow_add, Nat.add_sub_of_le (Nat.le_of_lt_succ (Finset.mem_range.mp hj))]
      rw [Finset.sum_congr rfl hp]
      simp [nsmul_eq_mul]
    simp_rw [he, add_mul, one_mul]
    simpa using (tendsto_self_mul_const_pow_of_lt_one ha0 ha1).add
      (tendsto_pow_atTop_nhds_zero_of_lt_one ha0 ha1)
  · have he (n : ℕ) : (∑ j ∈ Finset.range (n+1), a^j * b^(n-j)) =
        (a^(n+1)-b^(n+1))/(a-b) := by simpa using geom₂_sum hab (n+1)
    simp_rw [he, pow_succ]
    simpa using (((tendsto_pow_atTop_nhds_zero_of_lt_one ha0 ha1).mul_const a).sub
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hb0 hb1).mul_const b)).div_const (a-b)

theorem divided_power_sum_one_tendsto {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    Tendsto (fun n : ℕ => ∑ j ∈ Finset.range (n+1), 1^j * a^(n-j))
      atTop (𝓝 (1/(1-a))) := by
  have he (n : ℕ) : (∑ j ∈ Finset.range (n+1), (1:ℝ)^j * a^(n-j)) =
      (1-a^(n+1))/(1-a) := by simpa using geom₂_sum (ne_of_gt ha1) (n+1)
  simp_rw [he, pow_succ]
  simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1)).sub
    ((tendsto_pow_atTop_nhds_zero_of_lt_one ha0 ha1).mul_const a)).div_const (1-a)

/-- The exponentially small remainder survives the factor p in B4-1. -/
theorem normalizedTracePower_weighted_tail_tendsto (r : ι → ℝ) (i : ι) (hi : r i = 1)
    (h0 : ∀ j, 0 ≤ r j) (hgap : ∀ j, j ≠ i → r j < 1) :
    Tendsto (fun n : ℕ => (n:ℝ) * (normalizedTracePower r (n+1) - 1)) atTop (𝓝 0) := by
  have he (n : ℕ) : (n:ℝ) * (normalizedTracePower r (n+1) - 1) =
      ∑ j ∈ Finset.univ.erase i, (n:ℝ) * r j^(n+1) := by
    have hsum := Finset.sum_erase_add Finset.univ (fun j => r j^(n+1)) (Finset.mem_univ i)
    simp only [hi, one_pow] at hsum
    unfold normalizedTracePower
    rw [← hsum, add_sub_cancel_right, Finset.mul_sum]
  have ht (j : ι) (hj : j ∈ Finset.univ.erase i) :
      Tendsto (fun n : ℕ => (n:ℝ)*r j^(n+1)) atTop (𝓝 0) := by
    simpa only [pow_succ, ← mul_assoc, zero_mul] using
      (tendsto_self_mul_const_pow_of_lt_one (h0 j) (hgap j (Finset.ne_of_mem_erase hj))).mul_const (r j)
  simp_rw [he]
  simpa using tendsto_finset_sum (Finset.univ.erase i) ht

end PowerConvexity
