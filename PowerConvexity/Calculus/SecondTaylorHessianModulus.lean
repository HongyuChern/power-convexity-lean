import PowerConvexity.Calculus.QuadraticTaylor
import PowerConvexity.Calculus.RealHessianRules
import Mathlib.Analysis.Calculus.MeanValue

/-! # Actual quadratic Taylor approximation from an actual Hessian modulus.
Two applications of the normed-space mean value theorem are made on the
same closed ball. No unproved Taylor remainder estimate is assumed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def secondTaylorPolynomialZero (g : V → ℝ) (y : V) : ℝ :=
  g 0+fderiv ℝ g 0 y+((1/2 : ℝ) • realHessian g 0) y y

theorem secondTaylorPolynomialZero_isQuadratic {g : V → ℝ}
    (hg : ContDiffAt ℝ 2 g 0) : IsQuadraticPolynomial (secondTaylorPolynomialZero g) := by
  refine ⟨g 0,fderiv ℝ g 0,(1/2 : ℝ) • realHessian g 0,?_,fun _ => rfl⟩
  intro v w
  simp only [_root_.smul_apply,smul_eq_mul,realHessian_symm hg v w]

theorem secondTaylorPolynomialZero_value (g : V → ℝ) :
    secondTaylorPolynomialZero g 0 = g 0 := by simp [secondTaylorPolynomialZero]

theorem secondTaylorPolynomialZero_fderiv_zero {g : V → ℝ} (hg : ContDiffAt ℝ 2 g 0) :
    fderiv ℝ (secondTaylorPolynomialZero g) 0 = fderiv ℝ g 0 := by
  have hs : ∀ v w, ((1/2 : ℝ) • realHessian g 0) v w =
      ((1/2 : ℝ) • realHessian g 0) w v := by
    intro v w
    simp only [_root_.smul_apply,smul_eq_mul,realHessian_symm hg v w]
  exact (quadratic_coeff_hasFDerivAt (g 0) (fderiv ℝ g 0)
    ((1/2 : ℝ) • realHessian g 0) hs 0).fderiv.trans (by simp)

theorem secondTaylorPolynomialZero_hessian {g : V → ℝ} (hg : ContDiffAt ℝ 2 g 0) (x : V) :
    realHessian (secondTaylorPolynomialZero g) x = realHessian g 0 := by
  have hs : ∀ v w, ((1/2 : ℝ) • realHessian g 0) v w =
      ((1/2 : ℝ) • realHessian g 0) w v := by
    intro v w
    simp only [_root_.smul_apply,smul_eq_mul,realHessian_symm hg v w]
  change realHessian (fun y => g 0+fderiv ℝ g 0 y+((1/2 : ℝ) • realHessian g 0) y y) x = _
  simpa only [smul_smul,show (2:ℝ)*(1/2)=1 by norm_num,one_smul] using
    quadratic_coeff_realHessian (g 0) (fderiv ℝ g 0) ((1/2 : ℝ) • realHessian g 0) hs x

theorem actual_secondTaylor_error_of_hessian_modulus {g : V → ℝ} {R η : ℝ}
    (hR : 0 < R) (hη : 0 ≤ η)
    (hg : ∀ x ∈ closedBall (0 : V) R, ContDiffAt ℝ 2 g x)
    (hH : ∀ x ∈ closedBall (0 : V) R, ‖realHessian g x-realHessian g 0‖ ≤ η) :
    ∀ x ∈ closedBall (0 : V) R, |g x-secondTaylorPolynomialZero g x| ≤ η*R^2 := by
  have hzero : (0 : V) ∈ closedBall 0 R := mem_closedBall_self hR.le
  have hg0 := hg 0 hzero
  have hq := IsQuadraticPolynomial_contDiff (secondTaylorPolynomialZero_isQuadratic hg0) 2
  let F : V → ℝ := fun y => g y-secondTaylorPolynomialZero g y
  have hFC (x : V) (hx : x ∈ closedBall 0 R) : ContDiffAt ℝ 2 F x := (hg x hx).sub hq.contDiffAt
  have hF0 : F 0 = 0 := by simp [F,secondTaylorPolynomialZero_value]
  have hD0 : fderiv ℝ F 0 = 0 := by
    rw [show F = fun y => g y-secondTaylorPolynomialZero g y from rfl,
      fderiv_fun_sub (hg0.differentiableAt (by norm_num)) (hq.contDiffAt.differentiableAt (by norm_num)),
      secondTaylorPolynomialZero_fderiv_zero hg0,sub_self]
  have hFH (x : V) (hx : x ∈ closedBall 0 R) :
      realHessian F x = realHessian g x-realHessian g 0 := by
    rw [show F = fun y => g y-secondTaylorPolynomialZero g y from rfl,
      realHessian_sub_at (hg x hx) hq.contDiffAt,secondTaylorPolynomialZero_hessian hg0]
  have hD (x : V) (hx : x ∈ closedBall 0 R) : ‖fderiv ℝ F x‖ ≤ η*‖x‖ := by
    have hh := (convex_closedBall (0 : V) R).norm_image_sub_le_of_norm_fderiv_le
      (f := fderiv ℝ F)
      (fun y hy => ((hFC y hy).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
      (fun y hy => by change ‖realHessian F y‖ ≤ η; rw [hFH y hy]; exact hH y hy) hzero hx
    simpa only [hD0,sub_zero] using hh
  have hDR (x : V) (hx : x ∈ closedBall 0 R) : ‖fderiv ℝ F x‖ ≤ η*R :=
    (hD x hx).trans (mul_le_mul_of_nonneg_left
      (by simpa only [mem_closedBall,dist_zero_right] using hx) hη)
  intro x hx
  have hh := (convex_closedBall (0 : V) R).norm_image_sub_le_of_norm_fderiv_le
    (f := F) (fun y hy => (hFC y hy).differentiableAt (by norm_num)) hDR hzero hx
  have hh' : |F x| ≤ η*R*‖x‖ := by simpa only [hF0,sub_zero,Real.norm_eq_abs] using hh
  calc
    |g x-secondTaylorPolynomialZero g x| = |F x| := rfl
    _ ≤ η*R*‖x‖ := hh'
    _ ≤ η*R*R := mul_le_mul_of_nonneg_left
      (by simpa only [mem_closedBall,dist_zero_right] using hx) (mul_nonneg hη hR.le)
    _ = η*R^2 := by ring

end PowerConvexity
