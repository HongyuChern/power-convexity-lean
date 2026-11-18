import PowerConvexity.Calculus.PluriharmonicQuadratic
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Quantitative Hessian robustness from centered quadratic tests

Testing against negative real parts of rank-one holomorphic squares gives an
explicit lower Hessian bound.  The later L2-ball argument must prove that all
these concrete tests belong to the permitted perturbation ball.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem powerHessian_centered_perturbation {u q : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hq : ContDiffAt ℝ 2 q x) (hx : u x < 0)
    (hq0 : q x = 0) (hDq0 : fderiv ℝ q x = 0) (v w : E) :
    realHessian (powerTransform (fun y => u y + q y)) x v w =
      realHessian (powerTransform u) x v w + sqrtSlope (u x) * realHessian q x v w := by
  have hsum : u x + q x < 0 := by simpa only [hq0, add_zero] using hx
  rw [realHessian_powerTransform (hu.add hq) hsum,
    realHessian_powerTransform hu hx, realHessian_add hu hq,
    fderiv_fun_add (hu.differentiableAt (by norm_num)) (hq.differentiableAt (by norm_num))]
  simp only [hq0, hDq0, add_zero, add_apply, zero_apply]
  ring

theorem powerHessian_realPartSquare_test {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hx : u x < 0)
    (ell : E →L[ℝ] ℂ) (δ : ℝ) (v w : E) :
    realHessian (powerTransform (fun y => u y - δ * realPartSquare ell x y)) x v w =
      realHessian (powerTransform u) x v w -
        2 * δ * sqrtSlope (u x) * (ell v * ell w).re := by
  have hq : ContDiffAt ℝ 2 (fun y => -δ * realPartSquare ell x y) x :=
    contDiffAt_const.mul (realPartSquare_contDiff ell x 2).contDiffAt
  have hq0 : -δ * realPartSquare ell x x = 0 := by rw [realPartSquare_center, mul_zero]
  have hDq0 : fderiv ℝ (fun y => -δ * realPartSquare ell x y) x = 0 := by
    have hd := (realPartSquare_hasFDerivAt_center ell x).const_mul (-δ)
    simpa using hd.fderiv
  have he : (fun y => u y - δ * realPartSquare ell x y) =
      (fun y => u y + -δ * realPartSquare ell x y) := by funext y; ring
  rw [he, powerHessian_centered_perturbation hu hq hx hq0 hDq0,
    realHessian_const_mul, smul_apply, smul_apply, smul_eq_mul,
    realHessian_realPartSquare]
  ring

variable [InnerProductSpace ℂ E] [IsScalarTower ℝ ℂ E]

theorem exists_complex_norming_functional {v : E} (hv : v ≠ 0) :
    ∃ ell : E →L[ℂ] ℂ, ‖ell‖ = 1 ∧ ell v = (‖v‖ : ℂ) := by
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  refine ⟨(‖v‖⁻¹ : ℂ) • innerSL ℂ v, ?_, ?_⟩
  · rw [norm_smul, innerSL_apply_norm]
    simp [hn]
  · simp only [smul_apply, smul_eq_mul, innerSL_apply_apply, inner_self_eq_norm_sq_to_K,
      Complex.ofReal_pow, Complex.ofReal_inv]
    have hnC : (‖v‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn
    change (‖v‖ : ℂ)⁻¹ * (‖v‖ : ℂ)^2 = (‖v‖ : ℂ)
    field_simp [hnC]

/-- This is the quantitative analytic core of Appendix A robustness.  The
hypothesis tests actual polynomials, not arbitrary second-order jets. -/
theorem powerHessian_lower_of_holomorphic_square_tests {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hx : u x < 0) {δ : ℝ} (hδ : 0 ≤ δ)
    (htest : ∀ ell : E →L[ℂ] ℂ, ‖ell‖ = 1 → ∀ v : E,
      0 ≤ realHessian (powerTransform (fun y =>
        u y - δ * realPartSquare (ell.restrictScalars ℝ) x y)) x v v) :
    ∀ v : E, 2 * δ * sqrtSlope (u x) * ‖v‖^2 ≤
      realHessian (powerTransform u) x v v := by
  intro v
  by_cases hv : v = 0
  · simp [hv]
  obtain ⟨ell, hn, he⟩ := exists_complex_norming_functional hv
  have h := htest ell hn v
  rw [powerHessian_realPartSquare_test hu hx] at h
  simp only [ContinuousLinearMap.coe_restrictScalars', he,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at h
  nlinarith

end PowerConvexity
