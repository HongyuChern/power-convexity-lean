import PowerConvexity.Analysis.ActualInverseGraphJetFour
import PowerConvexity.Analysis.ActualSmallScaleDriftFour
import PowerConvexity.Analysis.ActualFlatFrozenEquationFour

/-! # Cancellation of the genuine graph drift in the original frozen equation -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
local notation "Mat" => Matrix (Fin (2+2)) (Fin (2+2)) ℝ
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_graph_drift_frozen_trace_four {N : E} {rho : E → ℝ} {a : E → Mat}
    (hrho0 : rho 0=0) (ha0 : a 0=1) :
    actualGraphShearDriftFieldFour N rho a 0=
      -(realBlockHessian realDirections imagDirections rho 0).trace • N := by
  have hPhi0 : actualGraphShearFour N rho 0=0 := by simp [actualGraphShearFour,hrho0]
  simp only [actualGraphShearDriftFieldFour,hPhi0,ha0,Matrix.one_apply,ite_mul,one_mul,
    zero_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  change -(∑ i : Fin (2+2),realHessian rho 0 (EuclideanSpace.single i 1)
    (EuclideanSpace.single i 1)) • N=_
  rw [actual_euclidean_trace_eq_block_trace_two]

theorem actual_inverse_graph_trace_four {N : E} {rho p : E → ℝ}
    (hrho : ContDiffAt ℝ 2 rho 0) (hrho0 : rho 0=0) (hD0 : fderiv ℝ rho 0=0)
    (hp : ContDiffAt ℝ 2 p 0) :
    (realBlockHessian realDirections imagDirections (p ∘ actualInverseGraphFour N rho) 0).trace=
      (realBlockHessian realDirections imagDirections p 0).trace-
        fderiv ℝ p 0 N*(realBlockHessian realDirections imagDirections rho 0).trace := by
  have hj := (actual_inverse_graph_composition_jets_four (N := N) hrho hrho0 hD0 hp).2
  rw [← actual_euclidean_trace_eq_block_trace_two,
    ← actual_euclidean_trace_eq_block_trace_two p 0,
    ← actual_euclidean_trace_eq_block_trace_two rho 0]
  simp_rw [hj]
  rw [Finset.sum_sub_distrib,← Finset.mul_sum]

theorem actual_inverse_graph_taylor_frozen_four {N : E} {rho p : E → ℝ} {a : E → Mat} {f0 : ℝ}
    (hrho : ContDiffAt ℝ 2 rho 0) (hrho0 : rho 0=0) (hD0 : fderiv ℝ rho 0=0)
    (ha0 : a 0=1) (hp : IsQuadraticPolynomial p)
    (hfreeze : (realBlockHessian realDirections imagDirections p 0).trace+
      fderiv ℝ p 0 (actualGraphShearDriftFieldFour N rho a 0) = -f0) :
    let P := secondTaylorPolynomialZero (p ∘ actualInverseGraphFour N rho)
    IsQuadraticPolynomial P ∧ fderiv ℝ P 0=fderiv ℝ p 0 ∧
      ∀ x, (realBlockHessian realDirections imagDirections P x).trace = -f0 := by
  dsimp only
  have hpC := (IsQuadraticPolynomial_contDiff hp 2).contDiffAt (x := (0 : E))
  have hPsi0 := actual_inverse_graph_value_four (N := N) hrho0
  have hp' : ContDiffAt ℝ 2 p (actualInverseGraphFour N rho 0) := by simpa only [hPsi0] using hpC
  have hg := hp'.comp 0 (actual_inverse_graph_contDiffAt_four (N := N) hrho)
  have hj := actual_inverse_graph_composition_jets_four (N := N) hrho hrho0 hD0 hpC
  refine ⟨secondTaylorPolynomialZero_isQuadratic hg,
    (secondTaylorPolynomialZero_fderiv_zero hg).trans hj.1,?_⟩
  intro x
  have hH : realBlockHessian realDirections imagDirections
      (secondTaylorPolynomialZero (p ∘ actualInverseGraphFour N rho)) x=
      realBlockHessian realDirections imagDirections (p ∘ actualInverseGraphFour N rho) 0 := by
    ext i j
    simp only [realBlockHessian,secondTaylorPolynomialZero_hessian hg]
  rw [hH,actual_inverse_graph_trace_four hrho hrho0 hD0 hpC]
  rw [actual_graph_drift_frozen_trace_four hrho0 ha0,map_smul,smul_eq_mul] at hfreeze
  nlinarith [hfreeze]

end PowerConvexity
