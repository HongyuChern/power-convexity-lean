import PowerConvexity.Calculus.RealHessianQuotient
import PowerConvexity.Calculus.HermitianDerivativeNormsTwo

/-! # Actual derivative and diagonal-contraction estimates under M + e A -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped ContDiff
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fderiv_norm_le_regularized {f g : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (e : ℝ) :
    ‖fderiv ℝ f x‖ ≤ ‖fderiv ℝ (fun y => f y+e*g y) x‖+|e| *‖fderiv ℝ g x‖ := by
  have heq : fderiv ℝ (fun y => f y+e*g y) x = fderiv ℝ f x+e • fderiv ℝ g x := by
    rw [fderiv_fun_add hf (hg.const_mul e),fderiv_const_mul hg e]
  calc
    _ = ‖fderiv ℝ (fun y => f y+e*g y) x-e • fderiv ℝ g x‖ := by rw [heq,add_sub_cancel_right]
    _ ≤ ‖fderiv ℝ (fun y => f y+e*g y) x‖+‖e • fderiv ℝ g x‖ := norm_sub_le _ _
    _ = _ := by rw [norm_smul,Real.norm_eq_abs]

theorem realHessian_regularized_contraction
    {f g : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x)
    (L : (E →L[ℝ] E →L[ℝ] ℝ) →ₗ[ℝ] ℝ) (e : ℝ) :
    L (realHessian (fun y => f y+e*g y) x) =
      L (realHessian f x)+e*L (realHessian g x) := by
  rw [realHessian_add hf (contDiffAt_const.mul hg),realHessian_const_mul_at hg e,map_add,map_smul,smul_eq_mul]

theorem regularized_diagonal_contraction_bound
    {f g : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x)
    (L : (E →L[ℝ] E →L[ℝ] ℝ) →ₗ[ℝ] ℝ)
    {e t T S Snew K B0 B1 B2 : ℝ}
    (he : 0 ≤ e) (ht : t ≤ T) (heT : 2*e ≤ T)
    (hK : 0 ≤ K) (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2)
    (hS : S ≤ Snew+4*e*K)
    (hLf : L (realHessian f x) ≤ B0*t+B1*S)
    (hLg : L (realHessian g x) ≤ B2) :
    L (realHessian (fun y => f y+e*g y) x) ≤
      (B0+2*B1*K+B2/2)*T+B1*Snew := by
  rw [realHessian_regularized_contraction hf hg L e]
  have h1 := mul_le_mul_of_nonneg_left ht hB0
  have h2 := mul_le_mul_of_nonneg_left hS hB1
  have h3 := mul_le_mul_of_nonneg_left hLg he
  have h4 := mul_le_mul_of_nonneg_right heT
    (show 0 ≤ 2*B1*K+B2/2 by positivity)
  nlinarith only [hLf,h1,h2,h3,h4]

theorem four_gradient_norms_le_regularized
    {a b c d A B C D : E → ℝ} {x : E}
    (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x)
    (hc : DifferentiableAt ℝ c x) (hd : DifferentiableAt ℝ d x)
    (hA : DifferentiableAt ℝ A x) (hB : DifferentiableAt ℝ B x)
    (hC : DifferentiableAt ℝ C x) (hD : DifferentiableAt ℝ D x)
    {e K : ℝ} (he : 0 ≤ e)
    (hDA : ‖fderiv ℝ A x‖ ≤ K) (hDB : ‖fderiv ℝ B x‖ ≤ K)
    (hDC : ‖fderiv ℝ C x‖ ≤ K) (hDD : ‖fderiv ℝ D x‖ ≤ K) :
    ‖fderiv ℝ a x‖+‖fderiv ℝ b x‖+‖fderiv ℝ c x‖+‖fderiv ℝ d x‖ ≤
      ‖fderiv ℝ (fun y => a y+e*A y) x‖+‖fderiv ℝ (fun y => b y+e*B y) x‖+
      ‖fderiv ℝ (fun y => c y+e*C y) x‖+‖fderiv ℝ (fun y => d y+e*D y) x‖+4*e*K := by
  have h1 := fderiv_norm_le_regularized ha hA e
  have h2 := fderiv_norm_le_regularized hb hB e
  have h3 := fderiv_norm_le_regularized hc hC e
  have h4 := fderiv_norm_le_regularized hd hD e
  rw [abs_of_nonneg he] at h1 h2 h3 h4
  have he1 := mul_le_mul_of_nonneg_left hDA he
  have he2 := mul_le_mul_of_nonneg_left hDB he
  have he3 := mul_le_mul_of_nonneg_left hDC he
  have he4 := mul_le_mul_of_nonneg_left hDD he
  linarith

end PowerConvexity
