import PowerConvexity.Calculus.ComplexScaledPullbackTwo
import PowerConvexity.Calculus.CMAJetsIsometricTransport

/-! # Actual translated and scaled pullback through the fixed complex frame.
The real scale cancels in the actual Hessian. All balls are actual metric balls
and the inverse isometry recovers the physical operator norm.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Set Metric
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
local notation "F" => DeGiorgi.AmbientSpace (2+2)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

def isometricScaledPullbackTwo (L : F ≃ₗᵢ[ℝ] E) (c : E) (r : ℝ)
    (w : E → ℝ) (x : F) : ℝ := (r^2)⁻¹*w (c+r • L x)

theorem isometric_scaled_point_distance_two (L : F ≃ₗᵢ[ℝ] E) (c : E)
    {r : ℝ} (hr : 0 < r) (x : F) : dist (c+r • L x) c = r*‖x‖ := by
  simp only [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,
    abs_of_pos hr,L.norm_map]

theorem isometricScaledPullbackTwo_realHessian (L : F ≃ₗᵢ[ℝ] E) (c : E)
    {r : ℝ} (hr : 0 < r) {w : E → ℝ} {x : F}
    (hw : ContDiffAt ℝ 2 w (c+r • L x)) (v z : F) :
    realHessian (isometricScaledPullbackTwo L c r w) x v z =
      realHessian w (c+r • L x) (L v) (L z) := by
  change realHessian (fun y => (r^2)⁻¹*w (c+r • L y)) x v z = _
  have hh := realHessian_normalized_affine L.toContinuousLinearEquiv.toContinuousLinearMap c
    (sq_pos_of_pos hr) (by simpa only [Real.sqrt_sq hr.le,
      ContinuousLinearEquiv.coe_coe,LinearIsometryEquiv.coe_toContinuousLinearEquiv] using hw) v z
  simpa only [Real.sqrt_sq hr.le,ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv,sub_eq_add_neg,realHessian_add_const] using hh

theorem isometricScaledPullbackTwo_complexHessian (L : F ≃ₗᵢ[ℝ] E) (c : E)
    {r : ℝ} (hr : 0 < r) {w : E → ℝ} {x : F}
    (hw : ContDiffAt ℝ 2 w (c+r • L x)) :
    complexHessian realDirections imagDirections (isometricScaledPullbackTwo L c r w) x =
      complexHessian (fun i => L (realDirections i)) (fun i => L (imagDirections i)) w (c+r • L x) := by
  change complexHessian realDirections imagDirections
    (fun y => (r^2)⁻¹*w (c+r • L y)) x = _
  have hh := complexHessian_normalized_affine L.toContinuousLinearEquiv.toContinuousLinearMap c
    (sq_pos_of_pos hr) (by simpa only [Real.sqrt_sq hr.le,
      ContinuousLinearEquiv.coe_coe,LinearIsometryEquiv.coe_toContinuousLinearEquiv] using hw)
    realDirections imagDirections
  simpa only [Real.sqrt_sq hr.le,ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv,sub_eq_add_neg,complexHessian_add_const] using hh

theorem isometricScaledPullbackTwo_recovers_norm (L : F ≃ₗᵢ[ℝ] E) (c : E)
    {r : ℝ} (hr : 0 < r) {w : E → ℝ} (hw : ContDiffAt ℝ 2 w c)
    {K : ℝ} (hK : 0 ≤ K)
    (hH : ‖realHessian (isometricScaledPullbackTwo L c r w) 0‖ ≤ K) :
    ‖realHessian w c‖ ≤ K := by
  apply ContinuousLinearMap.opNorm_le_bound _ hK
  intro v
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hK (norm_nonneg v))
  intro z
  have hreg : ContDiffAt ℝ 2 w (c+r • L (0:F)) := by simpa only [map_zero,smul_zero,add_zero] using hw
  have hh := isometricScaledPullbackTwo_realHessian L c hr hreg (L.symm v) (L.symm z)
  simp only [map_zero,smul_zero,add_zero,L.apply_symm_apply] at hh
  calc
    _ = ‖realHessian (isometricScaledPullbackTwo L c r w) 0 (L.symm v) (L.symm z)‖ := congrArg norm hh.symm
    _ ≤ ‖realHessian (isometricScaledPullbackTwo L c r w) 0‖*‖L.symm v‖*‖L.symm z‖ :=
      (realHessian (isometricScaledPullbackTwo L c r w) 0).le_opNorm₂ _ _
    _ ≤ K*‖v‖*‖z‖ := by rw [L.symm.norm_map,L.symm.norm_map]; gcongr

theorem isometricScaledPullbackTwo_local_data (L : F ≃ₗᵢ[ℝ] E) (c : E)
    {r ε : ℝ} (hr : 0 < r) {w : E → ℝ}
    (hwc : ContinuousOn w (closedBall c r)) (hw : ContDiffOn ℝ 2 w (ball c r))
    (hb : ∀ x ∈ closedBall c r, |w x| ≤ ε*r^2) :
    ContinuousOn (isometricScaledPullbackTwo L c r w) (closedBall 0 1) ∧
    ContDiffOn ℝ 2 (isometricScaledPullbackTwo L c r w) (ball 0 1) ∧
    (∀ x ∈ closedBall (0:F) 1, |isometricScaledPullbackTwo L c r w x| ≤ ε) := by
  have hmap (x : F) (hx : x ∈ closedBall 0 1) : c+r • L x ∈ closedBall c r := by
    rw [mem_closedBall,isometric_scaled_point_distance_two L c hr]
    exact mul_le_of_le_one_right hr.le (by simpa only [mem_closedBall,dist_zero_right] using hx)
  have hmapo (x : F) (hx : x ∈ ball 0 1) : c+r • L x ∈ ball c r := by
    rw [mem_ball,isometric_scaled_point_distance_two L c hr]
    exact mul_lt_of_lt_one_right hr (by simpa only [mem_ball,dist_zero_right] using hx)
  have hA : ContDiff ℝ 2 (fun x : F => c+r • L x) := by fun_prop
  refine ⟨continuousOn_const.mul (hwc.comp hA.continuous.continuousOn hmap),
    contDiffOn_const.mul (hw.comp hA.contDiffOn hmapo),?_⟩
  intro x hx
  change |(r^2)⁻¹*w (c+r • L x)| ≤ ε
  rw [abs_mul,abs_of_pos (inv_pos.mpr (sq_pos_of_pos hr))]
  calc
    _ ≤ (r^2)⁻¹*(ε*r^2) := mul_le_mul_of_nonneg_left (hb _ (hmap x hx)) (by positivity)
    _ = ε := by field_simp

end PowerConvexity
