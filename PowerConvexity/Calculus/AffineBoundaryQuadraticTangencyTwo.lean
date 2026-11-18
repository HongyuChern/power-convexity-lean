import PowerConvexity.Calculus.ComplexAffineTangentFieldTwo
import PowerConvexity.Calculus.LocalQuadraticRemainder

/-! # Quadratic tangency of actual affine holomorphic fields

The error is controlled by an actual second-order Taylor remainder. Subtracting
a scalar multiple of the defining function makes the entire first derivative
vanish; on its zero set this subtraction changes no value.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Matrix
open scoped ContDiff Topology BigOperators
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]

theorem exists_affine_complex_field_quadratic_tangency_two
    (e : Module.Basis (Fin 2) ℂ E) {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 3 f x) (hfx : f x = 0) (hDf : fderiv ℝ f x ≠ 0)
    (tau : E) (htau : fderiv ℝ f x tau = 0) :
    ∃ (K : E →L[ℂ] E) (c : E) (C : ℝ), 0 < C ∧
      (complexFieldMatrixTwo e K).trace.re = 0 ∧ c+K x = tau ∧
      ∃ delta > 0, ∀ y : E, ‖y-x‖ < delta → f y = 0 →
        |fderiv ℝ f y (c+K y)| ≤ C*‖y-x‖^2 := by
  obtain ⟨K,lam,htrace,hK⟩ := exists_complex_affine_tangent_linear_part_two
    e (fderiv ℝ f x) hDf (realHessian f x) tau
  let c : E := tau-K x
  have hcx : c+K x = tau := sub_add_cancel _ _
  have hf2 : ContDiffAt ℝ 2 f x := hf.of_le (by norm_num)
  let g : E → ℝ := fun y => fderiv ℝ f y (c+K y)
  let r : E → ℝ := fun y => g y-lam*f y
  have hg : ContDiffAt ℝ 2 g x :=
    (hf.fderiv_right (m := 2) (by norm_num)).clm_apply
      (contDiffAt_const.add (K.restrictScalars ℝ).contDiff.contDiffAt)
  have hr : ContDiffAt ℝ 2 r x := hg.sub (contDiffAt_const.mul hf2)
  have hrx : r x = 0 := by simp only [r,g,hcx,htau,hfx,mul_zero,sub_self]
  have hrd : fderiv ℝ r x = 0 := by
    have hd := (hg.differentiableAt (by norm_num)).hasFDerivAt.sub
      ((hf2.differentiableAt (by norm_num)).hasFDerivAt.const_mul lam)
    change HasFDerivAt r _ x at hd
    rw [hd.fderiv]
    ext v
    simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.zero_apply,smul_eq_mul]
    change fderiv ℝ g x v-lam*fderiv ℝ f x v = 0
    rw [show fderiv ℝ g x v = realHessian f x v (c+K x)+fderiv ℝ f x (K v) from
      fderiv_directional_affine_apply hf2 (K.restrictScalars ℝ) c v,hcx,hK v,
      realHessian_symm hf2 v tau]
    ring
  obtain ⟨C,hC,delta,hdelta,hbound⟩ := exists_local_quadratic_remainder_bound hr
  refine ⟨K,c,C,hC,htrace,hcx,delta,hdelta,?_⟩
  intro y hy hfy
  have hh := hbound y hy
  simpa only [hrx,hrd,ContinuousLinearMap.zero_apply,sub_zero,r,g,hfy,mul_zero] using hh

theorem complex_affine_field_contraction_zero_two
    (e : Module.Basis (Fin 2) ℂ E) (K : E →L[ℂ] E) (c : E)
    (htrace : (complexFieldMatrixTwo e K).trace.re = 0)
    {U : Set E} (hU : IsOpen U) {u : E → ℝ} (hu : ContDiffOn ℝ 3 u U)
    (hdet : ∀ y ∈ U, (complexHessian e (fun j => Complex.I • e j) u y).det = 1)
    {x : E} (hx : x ∈ U) :
    complexHessianContraction e (fun j => Complex.I • e j)
      (complexHessian e (fun j => Complex.I • e j) u x)⁻¹
      (realHessian (fun y => fderiv ℝ u y (c+K y)) x) = 0 := by
  obtain ⟨ha,hb⟩ := complexFieldMatrixTwo_frame e K
  have hh := affine_complex_field_linearized_trace_two hU hu e (fun j => Complex.I • e j)
    hdet (K.restrictScalars ℝ) c (complexFieldMatrixTwo e K) ha hb hx
  rw [htrace,mul_zero] at hh
  exact hh

end PowerConvexity
