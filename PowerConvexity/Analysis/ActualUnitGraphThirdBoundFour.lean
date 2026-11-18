import PowerConvexity.Analysis.ActualCommonPhysicalUnitGraphFour
import PowerConvexity.Analysis.ActualCommonGraphOriginalExpansionFour

/-! # A common actual graph third-derivative bound from the proved Hessian Lipschitz bound -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_unit_graph_third_bound_from_hessian_lipschitz_four
    {rho : E → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hLip : ∀ x ∈ closedBall (0 : E) 2, ∀ y ∈ closedBall (0 : E) 2,
      ‖realHessian rho x-realHessian rho y‖ ≤ K*‖x-y‖) :
    ∀ x ∈ closedBall (0 : E) 1, ‖fderiv ℝ (realHessian rho) x‖ ≤ K := by
  intro x hx
  have hx2 : x ∈ ball (0 : E) 2 := closedBall_subset_ball (by norm_num) hx
  apply norm_fderiv_le_of_lip' ℝ (f := realHessian rho) (x₀ := x) hK
  filter_upwards [isOpen_ball.mem_nhds hx2] with y hy
  exact hLip y (ball_subset_closedBall hy) x (ball_subset_closedBall hx2)

end PowerConvexity
