import PowerConvexity.Calculus.RealHessianRules
import CHS.Calculus.QuadraticPerturbation
import PowerConvexity.Calculus.TraceDetRatioRegularity

/-! # Actual real Frechet Hessian product and quotient rules -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
open Filter
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem realHessian_mul_real_at {f g : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) (v w : E) :
    realHessian (fun y => f y*g y) x v w =
      realHessian f x v w*g x+fderiv ℝ f x v*fderiv ℝ g x w+
        fderiv ℝ g x v*fderiv ℝ f x w+f x*realHessian g x v w := by
  have hdf := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdg := (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hfn := hf.eventually (by simp)
  have hgn := hg.eventually (by simp)
  have heq : fderiv ℝ (fun y => f y*g y) =ᶠ[𝓝 x]
      fun y => f y • fderiv ℝ g y+g y • fderiv ℝ f y := by
    filter_upwards [hfn,hgn] with y hyf hyg
    exact fderiv_fun_mul (hyf.differentiableAt (by norm_num)) (hyg.differentiableAt (by norm_num))
  have hp := ((hf.differentiableAt (by norm_num)).hasFDerivAt.smul hdg.hasFDerivAt).add
    ((hg.differentiableAt (by norm_num)).hasFDerivAt.smul hdf.hasFDerivAt)
  change HasFDerivAt (fun y => f y • fderiv ℝ g y+g y • fderiv ℝ f y) _ x at hp
  unfold realHessian
  rw [heq.fderiv_eq,hp.fderiv]
  simp only [add_apply,smul_apply,ContinuousLinearMap.smulRight_apply,smul_eq_mul]
  ring

theorem fderiv_real_inverse_at {f : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hx : f x ≠ 0) :
    fderiv ℝ (fun y => (f y)⁻¹) x = (-(f x^2)⁻¹) • fderiv ℝ f x :=
  ((hasDerivAt_inv hx).comp_hasFDerivAt x hf.hasFDerivAt).fderiv

theorem fderiv_real_div_at {f g : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (hx : g x ≠ 0) (v : E) :
    fderiv ℝ (fun y => f y/g y) x v =
      fderiv ℝ f x v/g x-f x*fderiv ℝ g x v/(g x)^2 := by
  change fderiv ℝ (fun y => f y*(g y)⁻¹) x v = _
  rw [fderiv_fun_mul hf (hg.fun_inv hx),fderiv_real_inverse_at hg hx]
  simp only [add_apply,smul_apply,smul_eq_mul]
  field_simp [hx]
  <;> ring

theorem realHessian_inverse_real_at {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hx : f x ≠ 0) (v w : E) :
    realHessian (fun y => (f y)⁻¹) x v w =
      (2*fderiv ℝ f x v*fderiv ℝ f x w-f x*realHessian f x v w)/(f x)^3 := by
  have heq : (fun y => f y*(f y)⁻¹) =ᶠ[𝓝 x] fun _ => (1:ℝ) := by
    filter_upwards [hf.continuousAt.eventually_ne hx] with y hy
    exact mul_inv_cancel₀ hy
  have hz : realHessian (fun y => f y*(f y)⁻¹) x v w = 0 := by
    unfold realHessian
    rw [heq.fderiv.fderiv_eq]
    simp
  rw [realHessian_mul_real_at hf (hf.fun_inv hx),
    fderiv_real_inverse_at (hf.differentiableAt (by norm_num)) hx] at hz
  simp only [smul_apply,smul_eq_mul] at hz
  field_simp [hx] at hz ⊢
  linear_combination hz

theorem realHessian_div_real_at {f g : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) (hx : g x ≠ 0) (v w : E) :
    realHessian (fun y => f y/g y) x v w =
      realHessian f x v w/g x-
        (fderiv ℝ f x v*fderiv ℝ g x w+fderiv ℝ g x v*fderiv ℝ f x w+
          f x*realHessian g x v w)/(g x)^2+
        2*f x*fderiv ℝ g x v*fderiv ℝ g x w/(g x)^3 := by
  change realHessian (fun y => f y*(g y)⁻¹) x v w = _
  rw [realHessian_mul_real_at hf (hg.fun_inv hx),realHessian_inverse_real_at hg hx,
    fderiv_real_inverse_at (hg.differentiableAt (by norm_num)) hx]
  simp only [smul_apply,smul_eq_mul]
  field_simp [hx]
  <;> ring

theorem realHessian_traceDetRatioTwo {t d : E → ℝ} {x : E}
    (ht : ContDiffAt ℝ 2 t x) (hd : ContDiffAt ℝ 2 d x) (hx : t x ≠ 0) (v w : E) :
    realHessian (fun y => traceDetRatioTwo (t y) (d y)) x v w =
      realHessian t x v w+realHessian d x v w/t x-
        (fderiv ℝ d x v*fderiv ℝ t x w+fderiv ℝ t x v*fderiv ℝ d x w+
          d x*realHessian t x v w)/(t x)^2+
        2*d x*fderiv ℝ t x v*fderiv ℝ t x w/(t x)^3 := by
  unfold traceDetRatioTwo
  rw [realHessian_add ht (hd.fun_div ht hx),add_apply,add_apply,realHessian_div_real_at hd ht hx]
  ring

end PowerConvexity
