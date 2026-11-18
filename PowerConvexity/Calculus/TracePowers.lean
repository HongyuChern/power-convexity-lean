import PowerConvexity.Calculus.MatrixIdentities

/-! # Actual noncommutative trace-power differentiation (Appendix B)

The matrices are differentiated entrywise by the existing real Wirtinger
operator. No formal derivative tensors are supplied as hypotheses.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped BigOperators ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem dz_matrix_trace {K : E → Matrix ι ι ℂ} {x : E}
    (hK : MatrixDifferentiableAt K x) (a b : E) :
    dz a b (fun y => (K y).trace) x = (matrixDZ a b K x).trace := by
  exact dz_sum_at (fun i => hK i i) a b

theorem matrix_power_differentiable {K : E → Matrix ι ι ℂ} {x : E}
    (hK : MatrixDifferentiableAt K x) (n : ℕ) :
    MatrixDifferentiableAt (fun y => K y ^ n) x := by
  induction n with
  | zero => intro i j; simpa using (differentiableAt_const ((1 : Matrix ι ι ℂ) i j))
  | succ n ih =>
    simpa only [pow_succ] using matrix_product_differentiable ih hK

theorem matrixDZ_power {K : E → Matrix ι ι ℂ} {x : E}
    (hK : MatrixDifferentiableAt K x) (a b : E) (n : ℕ) :
    matrixDZ a b (fun y => K y ^ n) x =
      ∑ j ∈ Finset.range n, K x ^ j * matrixDZ a b K x * K x ^ (n - 1 - j) := by
  induction n with
  | zero => simp [matrixDZ_const]
  | succ n ih =>
    simp only [pow_succ]
    rw [matrixDZ_product a b (matrix_power_differentiable hK n) hK, ih,
      Finset.sum_mul, Finset.sum_range_succ]
    simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, mul_one]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    have he : n - 1 - j + 1 = n - j := by
      have := Finset.mem_range.mp hj
      omega
    rw [mul_assoc, ← pow_succ, he]

theorem trace_power_derivative_sum (A V : Matrix ι ι ℂ) (n : ℕ) :
    (∑ j ∈ Finset.range n, A^j * V * A^(n - 1 - j)).trace =
      (n : ℂ) * (A^(n - 1) * V).trace := by
  rw [Matrix.trace_sum]
  have he (j : ℕ) (hj : j ∈ Finset.range n) :
      (A^j * V * A^(n - 1 - j)).trace = (A^(n - 1) * V).trace := by
    rw [Matrix.trace_mul_comm (A^j * V) (A^(n - 1 - j)), ← mul_assoc, ← pow_add]
    congr 3
    have := Finset.mem_range.mp hj
    omega
  rw [Finset.sum_congr rfl he]
  simp [nsmul_eq_mul]

theorem dz_trace_power {K : E → Matrix ι ι ℂ} {x : E}
    (hK : MatrixDifferentiableAt K x) (a b : E) (n : ℕ) :
    dz a b (fun y => (K y ^ n).trace) x =
      (n : ℂ) * (K x ^ (n - 1) * matrixDZ a b K x).trace := by
  rw [dz_matrix_trace (matrix_power_differentiable hK n) a b, matrixDZ_power hK,
    trace_power_derivative_sum]

theorem dz_mixed_trace_power {K : E → Matrix ι ι ℂ} {U : Set E}
    (hU : IsOpen U) (hK : ∀ i j, ContDiffOn ℝ 2 (fun y => K y i j) U)
    {x : E} (hx : x ∈ U) (a b c d : E) (n : ℕ) :
    dz c d (dz a b (fun y => (K y ^ (n + 1)).trace)) x =
      ((n + 1 : ℕ) : ℂ) *
        ((K x ^ n * matrixDZ c d (matrixDZ a b K) x).trace +
          ∑ j ∈ Finset.range n,
            (K x ^ j * matrixDZ c d K x * K x ^ (n - 1 - j) * matrixDZ a b K x).trace) := by
  have hKx : MatrixDifferentiableAt K x :=
    fun i j => ((hK i j).contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)
  have hDx := matrixDZ_differentiableAt
    (fun i j => (hK i j).contDiffAt (hU.mem_nhds hx)) a b
  have hpow := matrix_power_differentiable hKx n
  have he : dz a b (fun y => (K y ^ (n + 1)).trace) =ᶠ[𝓝 x]
      (fun y => ((n + 1 : ℕ) : ℂ) * (K y ^ n * matrixDZ a b K y).trace) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    simpa only [Nat.add_sub_cancel] using dz_trace_power
      (fun i j => ((hK i j).contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num)) a b (n + 1)
  rw [dz_congr_nhds he c d]
  have hTd : DifferentiableAt ℝ (fun y => (K y ^ n * matrixDZ a b K y).trace) x :=
    DifferentiableAt.fun_sum (fun i _ => matrix_product_differentiable hpow hDx i i)
  rw [dz_mul_at (differentiableAt_const ((n + 1 : ℕ) : ℂ)) hTd c d,
    dz_const, zero_mul, zero_add, dz_matrix_trace (matrix_product_differentiable hpow hDx),
    matrixDZ_product c d hpow hDx, matrixDZ_power hKx, Matrix.trace_add,
    Finset.sum_mul, Matrix.trace_sum]
  ring

end PowerConvexity
