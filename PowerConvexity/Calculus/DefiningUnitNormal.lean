import PowerConvexity.Calculus.ConvexDefiningCurvature
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! # The genuine normal derivative of a defining function

The normal is the normalized actual gradient. Its tangent quadratic form is
the actual defining Hessian divided by the gradient norm. No independent
formal shape operator is substituted for this derivative.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Filter
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def definingUnitNormal (f : E → ℝ) (x : E) : E :=
  ‖gradient f x‖⁻¹ • gradient f x

theorem definingGradient_hasFDerivAt {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) :
    HasFDerivAt (gradient f)
      (((InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
        (realHessian f x)) x := by
  have hd := ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasFDerivAt
  have h := (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp x hd
  unfold gradient
  simpa only [gradient,realHessian,Function.comp_def,ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv] using h

theorem definingGradient_ne_zero {f : E → ℝ} {x : E} (hDf : fderiv ℝ f x ≠ 0) :
    gradient f x ≠ 0 := by
  intro hz
  apply hDf
  rw [← toDual_gradient (f := f) (x := x),hz,map_zero]

theorem definingUnitNormal_norm {f : E → ℝ} {x : E} (hDf : fderiv ℝ f x ≠ 0) :
    ‖definingUnitNormal f x‖ = 1 := by
  rw [definingUnitNormal,norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (definingGradient_ne_zero hDf))

theorem definingUnitNormal_differentiableAt {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hDf : fderiv ℝ f x ≠ 0) :
    DifferentiableAt ℝ (definingUnitNormal f) x := by
  have hg := (definingGradient_hasFDerivAt hf).differentiableAt
  have hn := definingGradient_ne_zero hDf
  exact ((hg.norm ℝ hn).inv (norm_ne_zero_iff.mpr hn)).smul hg

theorem definingUnitNormal_fderiv_tangent_pair {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hDf : fderiv ℝ f x ≠ 0)
    (v w : E) (hw : fderiv ℝ f x w = 0) :
    inner ℝ (fderiv ℝ (definingUnitNormal f) x v) w =
      realHessian f x v w / ‖gradient f x‖ := by
  have hg := definingGradient_hasFDerivAt hf
  have hn := definingGradient_ne_zero hDf
  have hc := ((hg.differentiableAt.norm ℝ hn).inv (norm_ne_zero_iff.mpr hn)).hasFDerivAt
  have hd := hc.smul hg
  change HasFDerivAt (definingUnitNormal f) _ x at hd
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.comp_apply,
    inner_add_left,real_inner_smul_left,ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv,InnerProductSpace.toDual_symm_apply,
    inner_gradient_left,hw,Pi.inv_apply,zero_mul,mul_zero,add_zero,div_eq_mul_inv,mul_comm]

theorem definingUnitNormal_fderiv_normal_orthogonal {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hDf : fderiv ℝ f x ≠ 0) (v : E) :
    inner ℝ (gradient f x) (fderiv ℝ (definingUnitNormal f) x v) = 0 := by
  have hn := definingGradient_ne_zero hDf
  have hd := (definingUnitNormal_differentiableAt hf hDf).hasFDerivAt.norm_sq
  have he : (fun y => ‖definingUnitNormal f y‖^2) =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
    have hnear := (hf.fderiv_right (m := 1) (by norm_num)).continuousAt.tendsto.eventually
      (eventually_ne_nhds hDf)
    filter_upwards [hnear] with y hy
    rw [definingUnitNormal_norm hy,one_pow]
  have hz := he.fderiv_eq (𝕜 := ℝ)
  rw [hd.fderiv] at hz
  have hz0 : fderiv ℝ (fun _ : E => (1 : ℝ)) x = 0 := (hasFDerivAt_const (1 : ℝ) x).fderiv
  rw [hz0] at hz
  have hv := congrArg (fun D : E →L[ℝ] ℝ => D v) hz
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.smul_apply,
    innerSL_apply_apply,fderiv_const,ContinuousLinearMap.zero_apply,
    definingUnitNormal,real_inner_smul_left,smul_eq_mul] at hv
  simp only [two_smul ℕ] at hv
  have hp : 0 < ‖gradient f x‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hn)
  nlinarith

theorem definingUnitNormal_tangent_form_nonneg_of_convex
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) {x : E} (hx : x ∈ frontier U)
    {f : E → ℝ} (hf : ContDiffAt ℝ 2 f x) (hfx : f x = 0)
    (hDf : fderiv ℝ f x ≠ 0) (hdef : ∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0)
    (v : E) (hv : fderiv ℝ f x v = 0) :
    0 ≤ inner ℝ (fderiv ℝ (definingUnitNormal f) x v) v := by
  rw [definingUnitNormal_fderiv_tangent_pair hf hDf v v hv]
  exact div_nonneg (definingFunction_tangent_hessian_nonneg_of_convex hU hconv hx hf hfx hDf hdef v hv)
    (norm_nonneg _)

end PowerConvexity
