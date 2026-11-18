import CHS.Calculus.TangentNormalization
import PowerConvexity.Calculus.RealHessianRules

/-! # Actual tangent normalization with only local regularity

The affine term is the actual value and differential at the origin. The
potential is not assumed globally differentiable outside the working domain.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem actual_fderiv_tangentNormalized_at {u : E → ℝ} {x : E}
    (hu : DifferentiableAt ℝ u x) :
    fderiv ℝ (tangentNormalized u) x=fderiv ℝ u x-fderiv ℝ u 0 := by
  unfold tangentNormalized
  simpa only [Pi.sub_apply,fderiv_sub_const,ContinuousLinearMap.fderiv] using
    fderiv_fun_sub (hu.sub_const (u 0)) (fderiv ℝ u 0).differentiableAt

theorem actual_realHessian_tangentNormalized_at {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) :
    realHessian (tangentNormalized u) x=realHessian u x := by
  have he : (fun y => fderiv ℝ (tangentNormalized u) y) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ u y-fderiv ℝ u 0) := by
    filter_upwards [hu.eventually (by norm_num)] with y hy
    exact actual_fderiv_tangentNormalized_at (hy.differentiableAt (by norm_num))
  unfold realHessian
  rw [he.fderiv_eq,fderiv_sub_const]

theorem actual_complexHessian_tangentNormalized_at {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (a b : ι → E) :
    complexHessian a b (tangentNormalized u) x=complexHessian a b u x := by
  have hv : ContDiffAt ℝ 2 (tangentNormalized u) x :=
    (hu.sub contDiffAt_const).sub (fderiv ℝ u 0).contDiff.contDiffAt
  ext i j
  rw [complexHessian_real_entry hv,complexHessian_real_entry hu]
  simp only [actual_realHessian_tangentNormalized_at hu]

end PowerConvexity
