import PowerConvexity.Calculus.CMAJetsIsometricTransport
import PowerConvexity.Calculus.ActualThirdJetNormTwo

/-! # Actual first and second derivative norm bounds in the fixed real isometry -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open scoped ContDiff
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
attribute [local instance] atjInstance1 atjInstance2 atjInstance3 atjInstance4 atjInstance5 atjInstance6
local notation "F" => DeGiorgi.AmbientSpace (2+2)

theorem actual_fderiv_isometric_norm_bound_two
    (T : F ≃ₗᵢ[ℝ] E) {u : E → ℝ} {x : F} (hu : ContDiffAt ℝ 1 u (T x))
    {M : ℝ} (hM : 0 ≤ M) (hb : ‖fderiv ℝ u (T x)‖ ≤ M) :
    ‖fderiv ℝ (fun y => u (T y)) x‖ ≤ M := by
  let T0 : F →L[ℝ] E := T.toContinuousLinearEquiv.toContinuousLinearMap
  have he : fderiv ℝ (fun y => u (T y)) x = (fderiv ℝ u (T x)).comp T0 :=
    ((hu.differentiableAt (by norm_num)).hasFDerivAt.comp x T0.hasFDerivAt).fderiv
  rw [he]
  apply ContinuousLinearMap.opNorm_le_bound _ hM
  intro v
  change ‖fderiv ℝ u (T x) (T v)‖ ≤ M*‖v‖
  exact ((fderiv ℝ u (T x)).le_opNorm (T v)).trans
    (by simpa only [T.norm_map] using mul_le_mul_of_nonneg_right hb (norm_nonneg (T v)))

theorem actual_Hessian_isometric_norm_bound_two
    (T : F ≃ₗᵢ[ℝ] E) {u : E → ℝ} {x : F} (hu : ContDiffAt ℝ 2 u (T x))
    {M : ℝ} (hM : 0 ≤ M) (hb : ‖realHessian u (T x)‖ ≤ M) :
    ‖realHessian (fun y => u (T y)) x‖ ≤ M := by
  apply ContinuousLinearMap.opNorm_le_bound _ hM
  intro v
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hM (norm_nonneg v))
  intro w
  rw [realHessian_comp_linearIsometry T hu]
  exact ((realHessian u (T x)).le_opNorm₂ (T v) (T w)).trans
    (by simpa only [T.norm_map] using
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb (norm_nonneg (T v))) (norm_nonneg (T w)))

end PowerConvexity
