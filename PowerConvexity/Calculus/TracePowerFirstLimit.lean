import PowerConvexity.Calculus.TracePowerPaperFormulas
import PowerConvexity.Analysis.TracePowerNormalization

/-! # B3-1 and B3-4: limit of the actual trace-root first derivative -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem real_diagonal_trace_power (k : ι → ℝ) (p : ℕ) :
    (Matrix.diagonal (fun j => (k j:ℂ)) ^ p).trace = ((∑ j, k j^p : ℝ):ℂ) := by
  simp [Matrix.diagonal_pow, Matrix.trace, Matrix.diag_apply, ← Complex.ofReal_pow]

theorem real_diagonal_trace_power_pos (k : ι → ℝ) (i : ι)
    (hi : 0 < k i) (h0 : ∀ j, 0 ≤ k j) (p : ℕ) :
    0 < (Matrix.diagonal (fun j => (k j:ℂ)) ^ p).trace.re := by
  rw [real_diagonal_trace_power, Complex.ofReal_re]
  exact Finset.sum_pos' (fun j _ => pow_nonneg (h0 j) p)
    ⟨i, Finset.mem_univ i, pow_pos hi p⟩

theorem paper_B3_1_tracePowerRoot_first_limit {K : E → Matrix ι ι ℂ} {U : Set E}
    (hU : IsOpen U) (hK : ∀ i j, ContDiffOn ℝ 2 (fun y => K y i j) U)
    {x : E} (hx : x ∈ U) (k : ι → ℝ) (i : ι)
    (hdiag : K x = Matrix.diagonal (fun j => (k j:ℂ)))
    (hi : 0 < k i) (h0 : ∀ j, 0 ≤ k j) (hgap : ∀ j, j ≠ i → k j < k i)
    (hreal : ∀ n : ℕ, ∀ y ∈ U, (K y ^ (n+1)).trace.im = 0) (a b : E) :
    Filter.Tendsto (fun n : ℕ => dz a b (fun y => (tracePowerRoot K (n+1) y : ℂ)) x)
      Filter.atTop (𝓝 (dz a b (fun y => K y i i) x)) := by
  have hp (n : ℕ) : 0 < (K x^(n+1)).trace.re := by
    rw [hdiag]
    exact real_diagonal_trace_power_pos k i hi h0 (n+1)
  have he (n : ℕ) : dz a b (fun y => (tracePowerRoot K (n+1) y : ℂ)) x =
      (∑ j, (k j:ℂ)^n * matrixDZ a b K x j j) /
        (((∑ j, k j^(n+1)) ^ ((n:ℝ)/(n+1)) : ℝ):ℂ) := by
    rw [tracePowerRoot_dz hU hK hx n (hreal n) (hp n) a b, hdiag,
      trace_diagonal_power_mul, real_diagonal_trace_power, Complex.ofReal_re]
  simp_rw [he]
  exact trace_power_first_contraction_limit k i hi h0 hgap (fun j => matrixDZ a b K x j j)

end PowerConvexity
