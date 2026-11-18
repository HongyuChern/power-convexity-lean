import PowerConvexity.Calculus.StrictConvexity
import CHS.Calculus.HessianExtrema

/-! # Actual real Hessian rules needed by the gradient minimum principle -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff Topology

namespace PowerConvexity
open CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem realHessian_sub_at {u v : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x) :
    realHessian (fun y => u y - v y) x = realHessian u x - realHessian v x := by
  have hn : fderiv ℝ (fun y => u y - v y) =ᶠ[𝓝 x]
      fun y => fderiv ℝ u y - fderiv ℝ v y := by
    filter_upwards [hu.eventually (by simp), hv.eventually (by simp)] with y hyu hyv
    exact fderiv_fun_sub (hyu.differentiableAt (by norm_num))
      (hyv.differentiableAt (by norm_num))
  unfold realHessian
  rw [hn.fderiv_eq, fderiv_fun_sub
    ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
    ((hv.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))]

theorem realHessian_const_mul_at {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (c : ℝ) :
    realHessian (fun y => c * u y) x = c • realHessian u x := by
  have hn : fderiv ℝ (fun y => c * u y) =ᶠ[𝓝 x]
      fun y => c • fderiv ℝ u y := by
    filter_upwards [hu.eventually (by simp)] with y hy
    exact fderiv_fun_const_smul (hy.differentiableAt (by norm_num)) c
  unfold realHessian
  rw [hn.fderiv_eq, fderiv_fun_const_smul
    ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))]

theorem realHessian_neg (u : E → ℝ) (x : E) :
    realHessian (fun y => -u y) x = -realHessian u x := by
  have he : fderiv ℝ (fun y => -u y) = fun y => -fderiv ℝ u y :=
    funext fun _ => fderiv_fun_neg
  unfold realHessian
  rw [he, fderiv_fun_neg]

theorem realHessian_nonneg_of_isLocalMin {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hm : IsLocalMin u x) (v : E) :
    0 ≤ realHessian u x v v := by
  have h := realHessian_nonpos_of_isLocalMax hu.neg hm.neg v
  rw [realHessian_neg] at h
  simpa using h

theorem fderiv_eq_of_isLocalMin_sub {u v : E → ℝ} {x : E}
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x)
    (hm : IsLocalMin (fun y => u y - v y) x) : fderiv ℝ u x = fderiv ℝ v x := by
  have h := hm.fderiv_eq_zero
  rw [fderiv_fun_sub hu hv] at h
  exact sub_eq_zero.mp h

theorem realHessian_le_of_isLocalMin_sub {u v : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x)
    (hm : IsLocalMin (fun y => u y - v y) x) (w : E) :
    realHessian v x w w ≤ realHessian u x w w := by
  have h := realHessian_nonneg_of_isLocalMin (hu.sub hv) hm w
  rw [realHessian_sub_at hu hv] at h
  exact sub_nonneg.mp h

end PowerConvexity
