import PowerConvexity.Calculus.RealHessianRules
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! # Actual Hessian chain rule for a scalar outer function -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Filter
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem realHessian_scalar_composition
    {phi : ℝ → ℝ} (hphi : ContDiff ℝ 2 phi)
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (v w : E) :
    realHessian (fun y => phi (f y)) x v w =
      deriv phi (f x)*realHessian f x v w+
        deriv (deriv phi) (f x)*fderiv ℝ f x v*fderiv ℝ f x w := by
  have hpd : Differentiable ℝ phi := hphi.differentiable (by norm_num)
  have hpd1 : ContDiff ℝ 1 (deriv phi) :=
    (contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1+1) phi from hphi)).2.2
  have hpd2 : Differentiable ℝ (deriv phi) := hpd1.differentiable (by norm_num)
  have hfd : DifferentiableAt ℝ f x := hf.differentiableAt (by norm_num)
  have hdfd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hs := (hpd2 (f x)).hasDerivAt.comp_hasFDerivAt x hfd.hasFDerivAt
  have heq : fderiv ℝ (fun y => phi (f y)) =ᶠ[𝓝 x]
      (fun y => deriv phi (f y) • fderiv ℝ f y) := by
    filter_upwards [hf.eventually (by simp)] with y hy
    exact ((hpd (f y)).hasDerivAt.comp_hasFDerivAt y
      (hy.differentiableAt (by norm_num)).hasFDerivAt).fderiv
  unfold realHessian
  have hprod := (hs.smul hdfd.hasFDerivAt).fderiv
  change fderiv ℝ (fun y => deriv phi (f y) • fderiv ℝ f y) x = _ at hprod
  rw [heq.fderiv_eq,hprod]
  simp only [add_apply,smul_apply,ContinuousLinearMap.smulRight_apply,smul_eq_mul,Function.comp_apply]

end PowerConvexity
