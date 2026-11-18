import PowerConvexity.Analysis.ActualUniformRoughDomainDataFour
import PowerConvexity.Analysis.ActualUniformGraphZeroQuotientFour

/-! # The actual rough domain equation has a common graph boundary quotient -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_uniform_rough_domain_graph_quotient_four
    {lam Lambda B H F M : ℝ} (hlam : 0 < lam) (hLambda : lam ≤ Lambda)
    (hB : 0 ≤ B) (hH : 0 ≤ H) (hF : 0 ≤ F) (hM : 0 ≤ M) :
    ∃ R > 0, R ≤ (1/2 : ℝ) ∧ ∃ alpha : ℝ, 0 < alpha ∧ alpha < 1 ∧ ∃ C > 0,
      ∀ N : E, ‖N‖=1 → ∀ U : Set E, IsOpen U →
      ∀ D : ActualRoughDomainDirichletDataFour U lam Lambda F M,
      ∀ rho : E → ℝ,
      (∀ x ∈ closedBall (0 : E) 2, ContDiffAt ℝ 3 rho x) →
      (∀ x : E, ∀ t : ℝ, rho (x+t • N)=rho x) →
      (∀ x ∈ closedBall (0 : E) 2,
        actualGraphShearFour N rho x ∈ U ↔ 0 < inner ℝ N x) →
      (∀ x ∈ actualFlatUpperBallFour N 1, ‖fderiv ℝ rho x‖ ≤ B) →
      (∀ x ∈ actualFlatUpperBallFour N 1, ‖realHessian rho x‖ ≤ H) →
      ∃ q : ℝ, |q| ≤ C ∧ ∀ x ∈ actualFlatClosedUpperBallFour N R,
        |D.solution (actualGraphShearFour N rho x)-q*inner ℝ N x| ≤ C*‖x‖^alpha*inner ℝ N x := by
  obtain ⟨R,hR,hR2,alpha,ha,ha1,C,hC,hquot⟩ :=
    actual_uniform_graph_zero_boundary_quotient_four hlam hLambda hB
      (hlam.le.trans hLambda) hH hF hM
  refine ⟨R,hR,hR2,alpha,ha,ha1,C,hC,?_⟩
  intro N hN U hU D rho hrho hinv hmap hDB hHB
  have haC := fun i j => (D.regular i j).continuousOn
  have haN := actual_elliptic_operator_norm_pointwise_four hU D.coeff haC
  have hlo := actual_elliptic_bounds_pointwise_two hU D.coeff haC
  have hhi := actual_elliptic_inverse_coercivity_pointwise_four hU D.coeff haC D.positive
  have hInv : Lambda⁻¹ ≤ D.coeff.Λ⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le D.coeff.Λ_pos D.upper
  apply hquot N hN U hU rho D.solution D.source D.coeff.a hrho hinv hmap
    D.positive D.regular D.divergence ?_ hDB hHB ?_ ?_
    D.source_continuous D.source_bound D.solution_regular D.solution_continuous
    D.solution_zero D.solution_bound D.equation
  · intro x hx
    exact (haN _ ((hmap x (closedBall_subset_closedBall (by norm_num)
      (ball_subset_closedBall hx.1))).mpr hx.2)).trans D.upper
  · intro x hx v
    exact (mul_le_mul_of_nonneg_right D.lower (sq_nonneg _)).trans (hlo x hx v).1
  · intro x hx v
    exact (mul_le_mul_of_nonneg_right hInv (sq_nonneg _)).trans (hhi x hx v)

end PowerConvexity
