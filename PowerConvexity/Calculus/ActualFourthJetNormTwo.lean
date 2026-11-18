import PowerConvexity.Calculus.ActualHigherDerivativeIdentitiesTwo

/-! # Actual fourth derivative norm and modulus from scalar Hessian entries -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
open Filter
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
attribute [local instance] atjInstance1 atjInstance2 atjInstance3 atjInstance4 atjInstance5 atjInstance6
attribute [local instance] ahdTripleNormedGroup ahdTripleNormedSpace ahdTripleModule ahdTripleTopology

theorem actual_fourth_jet_norm_from_scalars_two
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 4 u x)
    {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ v w : E, ‖v‖ = 1 → ‖w‖ = 1 →
      ‖realHessian (fun y => realHessian u y v w) x‖ ≤ M) :
    ‖fderiv ℝ (fderiv ℝ (realHessian u)) x‖ ≤ M := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hM
  intro a ha
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hM
  intro b hbn
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hM
  intro v hv
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hM
  intro w hw
  rw [← actual_fourth_jet_scalar_identity_two hu v w a b]
  exact ((realHessian (fun y => realHessian u y v w) x).le_opNorm₂ a b).trans
    (by simpa only [ha,hbn,mul_one] using hb v w hv hw)

theorem actual_fourth_jet_difference_from_scalars_two
    {u : E → ℝ} {x y : E} (hux : ContDiffAt ℝ 4 u x) (huy : ContDiffAt ℝ 4 u y)
    {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ v w : E, ‖v‖ = 1 → ‖w‖ = 1 →
      ‖realHessian (fun z => realHessian u z v w) x-
        realHessian (fun z => realHessian u z v w) y‖ ≤ M) :
    ‖fderiv ℝ (fderiv ℝ (realHessian u)) x-
      fderiv ℝ (fderiv ℝ (realHessian u)) y‖ ≤ M := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hM
  intro a ha
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hM
  intro b hbn
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hM
  intro v hv
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hM
  intro w hw
  change ‖fderiv ℝ (fderiv ℝ (realHessian u)) x a b v w-
    fderiv ℝ (fderiv ℝ (realHessian u)) y a b v w‖ ≤ M
  rw [← actual_fourth_jet_scalar_identity_two hux v w a b,
    ← actual_fourth_jet_scalar_identity_two huy v w a b]
  have hh := (realHessian (fun z => realHessian u z v w) x-
    realHessian (fun z => realHessian u z v w) y).le_opNorm₂ a b
  exact hh.trans (by simpa only [ha,hbn,mul_one] using hb v w hv hw)

end PowerConvexity
