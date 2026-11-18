import PowerConvexity.Calculus.PositiveMatrixGradientSquareTwo
import PowerConvexity.Calculus.EllipticContactZero
import PowerConvexity.Calculus.MatrixZeroContactTwo

/-! # Vanishing of the full second jet of a semidefinite matrix field -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem realHessian_zero_of_two_sided_majorant
    {φ g : E → ℝ} {x : E} (hφ : ContDiffAt ℝ 2 φ x) (hg : ContDiffAt ℝ 2 g x)
    (hpos : ∀ᶠ y in 𝓝 x, 0 ≤ φ y+g y ∧ 0 ≤ φ y-g y)
    (hφ0 : φ x = 0) (hg0 : g x = 0) (hHφ : realHessian φ x = 0) :
    realHessian g x = 0 := by
  have hp : IsLocalMin (fun y => φ y+g y) x := by
    filter_upwards [hpos] with y hy
    simpa only [hφ0,hg0,zero_add] using hy.1
  have hm : IsLocalMin (fun y => φ y-g y) x := by
    filter_upwards [hpos] with y hy
    simpa only [hφ0,hg0,sub_zero] using hy.2
  have hquad (v : E) : realHessian g x v v = 0 := by
    have ha := realHessian_nonneg_of_isLocalMin (hφ.add hg) hp v
    have hb := realHessian_nonneg_of_isLocalMin (hφ.sub hg) hm v
    rw [realHessian_add hφ hg,hHφ] at ha
    rw [realHessian_sub_at hφ hg,hHφ] at hb
    have ha' : 0 ≤ realHessian g x v v := by
      simpa only [ContinuousLinearMap.add_apply,ContinuousLinearMap.zero_apply,zero_add] using ha
    have hb' : 0 ≤ -realHessian g x v v := by
      simpa only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.zero_apply,zero_sub,ContinuousLinearMap.neg_apply] using hb
    linarith
  ext v w
  have hh := hquad (v+w)
  simp only [map_add,ContinuousLinearMap.add_apply] at hh
  rw [hquad v,hquad w,realHessian_symm hg w v] at hh
  change realHessian g x v w = 0
  linarith

theorem matrix_real_imag_Hessians_zero_of_trace_Hessian_zero_two
    {M : E → Matrix (Fin 2) (Fin 2) ℂ} {x : E}
    (hM : ∀ i j, ContDiffAt ℝ 2 (fun y => M y i j) x)
    (hpos : ∀ᶠ y in 𝓝 x, (M y).PosSemidef) (hzero : M x = 0)
    (htrace : realHessian (fun y => (M y).trace.re) x = 0) :
    ∀ i j, realHessian (fun y => (M y i j).re) x = 0 ∧
      realHessian (fun y => (M y i j).im) x = 0 := by
  intro i j
  constructor
  · apply realHessian_zero_of_two_sided_majorant (matrix_trace_re_contDiffAt_two hM)
      (Complex.reCLM.contDiff.contDiffAt.comp x (hM i j)) _ (by simp [hzero]) (by simp [hzero]) htrace
    filter_upwards [hpos] with y hy
    have hh := abs_le.mp (posSemidef_two_entry_trace_bounds hy i j).1
    constructor <;> dsimp only [Function.comp_def,Complex.reCLM_apply] <;> linarith
  · apply realHessian_zero_of_two_sided_majorant (matrix_trace_re_contDiffAt_two hM)
      (Complex.imCLM.contDiff.contDiffAt.comp x (hM i j)) _ (by simp [hzero]) (by simp [hzero]) htrace
    filter_upwards [hpos] with y hy
    have hh := abs_le.mp (posSemidef_two_entry_trace_bounds hy i j).2
    constructor <;> dsimp only [Function.comp_def,Complex.imCLM_apply] <;> linarith

end PowerConvexity
