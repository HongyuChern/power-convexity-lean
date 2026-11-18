import PowerConvexity.Analysis.ActualC2CMADirectionalWeakTwo
import PowerConvexity.Analysis.ActualScalarWeakFluxTwo
import PowerConvexity.Analysis.ActualLocalClassicalWeakTwo

/-! # The genuine C2 first variation on the full H01 test space

The scalar source is exactly -c^{-1} D_v rho.  The same actual first
derivative has its local Sobolev witness; no C3 premise is introduced.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] atjInstance1 atjInstance2 atjInstance3 atjInstance4 atjInstance5 atjInstance6

theorem actual_C2_scaled_cofactor_first_variation_weak_ball_two
    {U : Set E} (hU : IsOpen U) {u rho : E → ℝ}
    (hu : ContDiffOn ℝ 2 u U) (hrho : ContDiffOn ℝ 1 rho U)
    (hdet : ∀ x ∈ U, (complexHessian realDirections imagDirections u x).det.re=rho x)
    {c : ℝ} (A : EllipticCoeff (2+2) U)
    (hA : ∀ x ∈ U, A.a x=c⁻¹ • complexCofactorCoeff u x)
    {x₀ : E} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hclosed : closedBall x₀ R ⊆ U) (v : E) :
    ActualScalarWeakEquationTwo
      (A.restrict (ball_subset_closedBall.trans ((closedBall_subset_closedBall hrR.le).trans hclosed)))
      (fun x => -(c⁻¹*fderiv ℝ rho x v)) (fun x => fderiv ℝ u x v) := by
  let p : E → ℝ := fun x => fderiv ℝ u x v
  let f : E → ℝ := fun x => -(c⁻¹*fderiv ℝ rho x v)
  have hsmall : closedBall x₀ r ⊆ U := (closedBall_subset_closedBall hrR.le).trans hclosed
  have hsub : ball x₀ r ⊆ U := ball_subset_closedBall.trans hsmall
  have hp : ContDiffOn ℝ 1 p U :=
    (hu.fderiv_of_isOpen hU (m := 1) (by norm_num)).clm_apply contDiffOn_const
  have hfc : ContinuousOn f U :=
    (continuousOn_const.mul
      ((hrho.fderiv_of_isOpen hU (m := 0) (by norm_num)).continuousOn.clm_apply continuousOn_const)).neg
  have hf := continuousOn_memLp_two_of_subset_compact measurableSet_ball
    (isCompact_closedBall x₀ r) ball_subset_closedBall (hfc.mono hsmall)
  have hraw := actual_C2_CMA_directional_hasWeakDiv_two hU hu hrho hdet hr hrR hclosed v
  have hscaled := actual_hasWeakDiv_const_smul_two hraw c⁻¹
  have hdiv : HasWeakDiv (fun x => -f x)
      (fun x => matMulE (A.a x) (smoothGradField p x)) (ball x₀ r) := by
    apply actual_hasWeakDiv_congr_on_two isOpen_ball hscaled
    · intro x hx
      change c⁻¹ • matMulE (complexCofactorCoeff u x) (smoothGradField p x)=
        matMulE (A.a x) (smoothGradField p x)
      rw [hA x (hsub hx),matMulE_smul_matrix]
    · intro x hx
      dsimp only [f]
      ring
  exact actual_scalar_weak_of_weak_flux_two isOpen_ball isBounded_ball (A.restrict hsub)
    (actualLocalClassicalBallWitnessTwo hU hp hsmall)
    (Filter.Eventually.of_forall (fun _ => rfl)) hf (fun _ _ => rfl) hdiv

end PowerConvexity
