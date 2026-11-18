import PowerConvexity.Calculus.NormalizedSchurAllRowsBoundTwo
import PowerConvexity.Calculus.HermitianDerivativeNormsTwo
import PowerConvexity.Calculus.ComplexGradientMinimum
import PowerConvexity.Calculus.MatrixZeroContactTwo

/-! # Actual Schur diagonal estimates in the real coefficients used by the ratio -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Filter
open scoped ContDiff Topology BigOperators ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem matrixL_diagonal_re_eq_complexLinearized
    (a b : Fin 2 → E) (u : E → ℝ) {M : E → Matrix (Fin 2) (Fin 2) ℂ} {x : E}
    (hherm : ∀ᶠ y in 𝓝 x, (M y).IsHermitian) (i : Fin 2) :
    (matrixL a b u M x i i).re = complexLinearized a b u (fun y => (M y i i).re) x := by
  have hr : (fun y => M y i i) =ᶠ[𝓝 x] fun y => ((M y i i).re:ℂ) := by
    filter_upwards [hherm] with y hy
    have hh := congrArg Complex.im (hy.apply i i)
    change -(M y i i).im = (M y i i).im at hh
    apply Complex.ext
    · rfl
    · simp only [Complex.ofReal_im]
      linarith
  rw [matrixL_entry]
  unfold complexLinearized
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  rw [dz_dz_congr_eventually hr (a p) (b p) (a q) (-b q)]

theorem matrixL_diagonal_re_eq_real_contraction
    (a b : Fin 2 → E) (u : E → ℝ) {M : E → Matrix (Fin 2) (Fin 2) ℂ} {x : E}
    (hherm : ∀ᶠ y in 𝓝 x, (M y).IsHermitian) (i : Fin 2)
    (hMi : ContDiffAt ℝ 2 (fun y => (M y i i).re) x) :
    (matrixL a b u M x i i).re =
      complexHessianContraction a b (complexHessian a b u x)⁻¹
        (realHessian (fun y => (M y i i).re) x) := by
  rw [matrixL_diagonal_re_eq_complexLinearized a b u hherm i,complexLinearized_eq_real a b u hMi]

theorem modifiedSchur_real_diagonal_trace_bound_two {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : Fin 2 → E)
    {ρ : ℂ} (hρ : ρ ≠ 0)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = ρ)
    (hneg : ∀ y ∈ U, u y < 0)
    (hpos : ∀ y ∈ U, (complexHessian a b u y).PosDef)
    {x : E} (hx : x ∈ U) (d : Fin 2 → ℝ)
    (hI : modifiedA a b u x = 1)
    (hD : modifiedB a b u x = Matrix.diagonal (fun i => (d i:ℂ)))
    (hd : ∀ i, 0 ≤ d i ∧ d i ≤ 1)
    {B : ℝ} (hB : 1 ≤ B) (hdir : ∀ p, (‖a p‖+‖b p‖)/2 ≤ B) (k : Fin 2)
    (hjets : normalizedSpectralJetBoundTwo
      (a ∘ Equiv.swap (0:Fin 2) k) (b ∘ Equiv.swap (0:Fin 2) k) u x B) :
    complexHessianContraction a b (complexHessian a b u x)⁻¹
      (realHessian (fun y => (modifiedSchur a b u y k k).re) x) ≤
      (768*B^5+96*B^3)*(2-(d 0)^2-(d 1)^2)+
        48*B^3*hermitianDerivativeSumTwo (modifiedSchur a b u) x := by
  have hM := modifiedSchur_contDiffAt_two (hu.contDiffAt (hU.mem_nhds hx))
    (hneg x hx) a b (hpos x hx)
  have hherm : ∀ᶠ y in 𝓝 x, (modifiedSchur a b u y).IsHermitian := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact modifiedSchur_isHermitian ((hu.contDiffAt (hU.mem_nhds hy)).of_le (by norm_num))
      (hneg y hy) a b (hpos y hy)
  rw [← matrixL_diagonal_re_eq_real_contraction a b u hherm k
    (Complex.reCLM.contDiff.contDiffAt.comp x (hM k k))]
  apply modifiedSchur_LM_normalized_all_rows_fderiv_bound_two hU hu a b hρ hdet hneg hpos
    hx d hI hD hd hB (hermitianDerivativeSumTwo_nonneg _ x) hdir k hjets
  intro s
  exact hermitian_matrix_entry_fderiv_norm_le_sum_two
    (fun i j => (hM i j).differentiableAt (by norm_num)) hherm k s

end PowerConvexity
