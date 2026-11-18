import PowerConvexity.Calculus.AffineDirectionalHessian

/-! # Actual third derivative norms from the scalar first variations -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open Filter
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
local instance atjInstance1 : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance atjInstance2 : Module ℝ (E →L[ℝ] ℝ) :=
  (inferInstance : NormedSpace ℝ (E →L[ℝ] ℝ)).toModule
local instance atjInstance3 : TopologicalSpace (E →L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance atjInstance4 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance atjInstance5 : Module ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  (inferInstance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ)).toModule
local instance atjInstance6 : TopologicalSpace (E →L[ℝ] E →L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace


theorem actual_third_jet_directional_identity_two
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 3 u x) (v a b : E) :
    realHessian (fun y => fderiv ℝ u y v) x a b =
      fderiv ℝ (realHessian u) x a b v := by
  simpa only [ContinuousLinearMap.zero_apply,map_zero,add_zero] using
    realHessian_directional_affine_formula hu (0 : E →L[ℝ] E) v a b

theorem actual_third_jet_norm_from_directional_two
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 3 u x)
    {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ v : E, ‖v‖ = 1 → ‖realHessian (fun y => fderiv ℝ u y v) x‖ ≤ M) :
    ‖fderiv ℝ (realHessian u) x‖ ≤ M := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hM
  intro a ha
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hM
  intro b hbn
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hM
  intro v hv
  rw [← actual_third_jet_directional_identity_two hu v a b]
  exact ((realHessian (fun y => fderiv ℝ u y v) x).le_opNorm₂ a b).trans
    (by simpa only [ha,hbn,mul_one] using hb v hv)

theorem actual_third_jet_difference_from_directional_two
    {u : E → ℝ} {x y : E} (hux : ContDiffAt ℝ 3 u x) (huy : ContDiffAt ℝ 3 u y)
    {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ v : E, ‖v‖ = 1 →
      ‖realHessian (fun z => fderiv ℝ u z v) x-realHessian (fun z => fderiv ℝ u z v) y‖ ≤ M) :
    ‖fderiv ℝ (realHessian u) x-fderiv ℝ (realHessian u) y‖ ≤ M := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hM
  intro a ha
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hM
  intro b hbn
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hM
  intro v hv
  change ‖fderiv ℝ (realHessian u) x a b v-fderiv ℝ (realHessian u) y a b v‖ ≤ M
  rw [← actual_third_jet_directional_identity_two hux v a b,
    ← actual_third_jet_directional_identity_two huy v a b]
  have hh := (realHessian (fun z => fderiv ℝ u z v) x-
    realHessian (fun z => fderiv ℝ u z v) y).le_opNorm₂ a b
  exact hh.trans (by simpa only [ha,hbn,mul_one] using hb v hv)

end PowerConvexity
