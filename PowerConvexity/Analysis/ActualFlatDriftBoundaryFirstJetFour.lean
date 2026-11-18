import PowerConvexity.Analysis.ActualFlatDriftGeneralExpansionFour
import PowerConvexity.Analysis.ActualFlatBoundaryFirstDerivativeFour

/-! # The actual boundary first derivative of the full drift equation -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory Asymptotics
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_flat_drift_boundary_firstJet_four {lam Lambda alpha F : ℝ}
    (hlam : 0 < lam) (hLambda : 0 < Lambda) (halpha : 0 < alpha) (halpha1 : alpha ≤ 1) (hF : 0 ≤ F) :
    ∃ C > 0, ∃ beta : ℝ, 0 < beta ∧ beta < 1 ∧ ∃ M ≥ 0,
      ∀ N : E, ‖N‖=1 → ∃ kappa > 0, kappa ≤ 1 ∧
      ∀ D : ActualFlatDriftIterationInputFour N lam Lambda alpha kappa, |D.source 0| ≤ F →
      ∃ p : E → ℝ, IsQuadraticPolynomial p ∧
        (∀ x : E, inner ℝ N x=0 → p x=0) ∧
        HasFDerivWithinAt D.solution (fderiv ℝ p 0) {x : E | 0 ≤ inner ℝ N x} 0 ∧
        ‖fderiv ℝ p 0‖ ≤ C ∧ (∀ x, ‖realHessian p x‖ ≤ C) ∧
        (realBlockHessian realDirections imagDirections p 0).trace+
          fderiv ℝ p 0 (D.drift 0) = -D.source 0 ∧
        (∀ v : E, fderiv ℝ p 0 v=inner ℝ N v*fderiv ℝ p 0 N) ∧
        ∀ x : E, 0 ≤ inner ℝ N x → ‖x‖ < (1/2 : ℝ) →
          |D.solution x-p x| ≤ M*‖x‖^2*‖x‖^beta := by
  obtain ⟨C,hC,r,hr,hr8,_,hexp⟩ :=
    actual_flat_drift_general_quadratic_expansion_four hlam hLambda halpha halpha1 hF
  obtain ⟨beta,hbeta,hbeta1,M,hM,hrem⟩ := actual_flat_geometric_remainder_holder_four
    (R := 1) zero_lt_one hr (hr8.trans_lt (by norm_num)) hC.le
  refine ⟨C,hC,beta,hbeta,hbeta1,M,hM,?_⟩
  intro N hN
  obtain ⟨kappa,hk,hk1,hP⟩ := hexp N hN
  refine ⟨kappa,hk,hk1,?_⟩
  intro D hf0
  obtain ⟨p,hp,hp0,hpt,hpD,hpH,herr⟩ := hP D hf0
  have hzero : D.solution 0=p 0 := by
    rw [D.solution_zero 0 (mem_closedBall_self (by norm_num)) (by simp),hp0 0 (by simp)]
  have hpoint : ∀ x : E, 0 ≤ inner ℝ N x → ‖x‖ < (1/2 : ℝ) →
      |D.solution x-p x| ≤ M*‖x‖^2*‖x‖^beta :=
    hrem N D.solution p hzero (by simpa only [one_mul] using herr)
  exact ⟨p,hp,hp0,actual_flat_remainder_hasFDerivWithinAt_four hp zero_lt_one hM hbeta.le hpoint,
    hpD,hpH,hpt,actual_flat_quadratic_fderiv_normal_four hN hp hp0,hpoint⟩

end PowerConvexity
