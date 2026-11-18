import PowerConvexity.Analysis.TracePowerSecondNormalization

/-! # The actual B4 matrix contraction in normalized spectral variables -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped BigOperators Topology
namespace PowerConvexity
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem trace_diagonal_convolution_sum (k : ι → ℝ) (X Y : Matrix ι ι ℂ) (n : ℕ) :
    (∑ j ∈ Finset.range (n+1),
      (Matrix.diagonal (fun l => (k l:ℂ)) ^ j * Y *
        Matrix.diagonal (fun l => (k l:ℂ)) ^ (n-j) * X).trace) =
      ∑ l, ∑ m, ((∑ j ∈ Finset.range (n+1), k l^j*k m^(n-j) : ℝ):ℂ)*Y l m*X m l := by
  simp_rw [trace_diagonal_mixed_powers]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  push_cast
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem trace_second_contraction_normalize (k : ι → ℝ) (i : ι)
    (hi : 0 < k i) (h0 : ∀ j, 0 ≤ k j) (X Y : Matrix ι ι ℂ) (n : ℕ) :
    let D : Matrix ι ι ℂ := Matrix.diagonal (fun j => (k j:ℂ))
    let T : ℝ := ∑ j, k j^(n+2)
    (∑ j ∈ Finset.range (n+1), (D^j*Y*D^(n-j)*X).trace) /
        ((T^(((n:ℝ)+1)/((n:ℝ)+2)):ℝ):ℂ) -
      ((n:ℂ)+1)*(D^(n+1)*X).trace*(D^(n+1)*Y).trace /
        ((T^((2*((n:ℝ)+2)-1)/((n:ℝ)+2)):ℝ):ℂ) =
      (k i:ℂ)⁻¹ * ∑ l, ∑ m, normalizedTraceSecondPair (fun j => k j/k i) X Y l m n := by
  dsimp only
  rw [trace_diagonal_convolution_sum, trace_diagonal_power_mul, trace_diagonal_power_mul]
  rw [Finset.sum_div]
  simp_rw [Finset.sum_div]
  rw [Finset.mul_sum Finset.univ (fun l => (k l:ℂ)^(n+1)*X l l) ((n:ℂ)+1), Finset.sum_mul, Finset.sum_div]
  simp_rw [Finset.mul_sum, Finset.sum_div]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro l _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m _
  have hC := congrArg Complex.ofReal (trace_power_convolution_coefficient_normalize k i hi h0 l m n)
  have hR := congrArg Complex.ofReal (trace_power_rank_coefficient_normalize k i hi h0 l m n)
  push_cast at hC hR
  change _ = (k i:ℂ)⁻¹ * (_*Y l m*X m l - _*X l l*Y m m)
  calc
    _ = (((∑ j ∈ Finset.range (n+1), k l^j*k m^(n-j):ℝ):ℂ) /
        (((∑ j, k j^(n+2))^(((n:ℝ)+1)/((n:ℝ)+2)):ℝ):ℂ)) *Y l m*X m l -
        (((n:ℂ)+1)*(k l:ℂ)^(n+1)*(k m:ℂ)^(n+1) /
        (((∑ j, k j^(n+2))^((2*((n:ℝ)+2)-1)/((n:ℝ)+2)):ℝ):ℂ)) * X l l*Y m m := by ring
    _ = _ := by
      push_cast
      rw [hC,hR]
      ring

end PowerConvexity
