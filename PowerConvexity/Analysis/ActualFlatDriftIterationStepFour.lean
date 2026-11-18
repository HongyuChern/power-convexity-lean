import PowerConvexity.Analysis.ActualFlatDriftIterationDataFour
import PowerConvexity.Analysis.ActualFlatDriftFrozenUpdateFour

/-! # One actual drift iteration step with both first- and second-jet control -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

structure ActualFlatDriftQuadraticStateFour (N : E) (u : E → ℝ) (b0 : E) (f0 R a M K : ℝ) where
  polynomial : E → ℝ
  quadratic : IsQuadraticPolynomial polynomial
  zero : ∀ x : E, inner ℝ N x=0 → polynomial x=0
  frozen : (realBlockHessian realDirections imagDirections polynomial 0).trace+
    fderiv ℝ polynomial 0 b0 = -f0
  gradient : ‖fderiv ℝ polynomial 0‖ ≤ 2*K*(1-a)
  hessian : ‖realHessian polynomial 0‖ ≤ 2*M*(1-a)
  error : ∀ x ∈ actualFlatClosedUpperBallFour N R, |u x-polynomial x| ≤ a*R^2

theorem actual_flat_drift_quadratic_iteration_step_four
    {N : E} (hN : ‖N‖=1) {lam Lambda alpha kappa R a r M K delta : ℝ}
    (halpha : 0 < alpha) (halpha1 : alpha ≤ 1) (hk : 0 ≤ kappa)
    (hR : 0 < R) (hR1 : R ≤ 1) (ha : 0 < a) (hM : 0 < M) (hK : 0 < K)
    (hRa : R^alpha ≤ a) (hsmall : kappa*(1+34*M+2*K) ≤ delta)
    (D : ActualFlatDriftIterationInputFour N lam Lambda alpha kappa)
    (hstep : ∀ B : ActualFlatDriftPerturbationDataFour N lam Lambda delta,
      ContinuousOn B.drift (actualFlatClosedUpperBallFour N 1) →
      ContinuousOn B.source (actualFlatClosedUpperBallFour N 1) →
      ∃ p : E → ℝ, IsQuadraticPolynomial p ∧
        (∀ x : E, inner ℝ N x=0 → p x=0) ∧
        (realBlockHessian realDirections imagDirections p 0).trace+
          fderiv ℝ p 0 (B.drift 0) = -B.source 0 ∧
        ‖fderiv ℝ p 0‖ ≤ K ∧ (∀ x, ‖realHessian p x‖ ≤ M) ∧
        ∀ x ∈ actualFlatClosedUpperBallFour N r, |B.solution x-p x| ≤ (1/2 : ℝ)*r^2)
    (S : ActualFlatDriftQuadraticStateFour N D.solution (D.drift 0) (D.source 0) R a M K) :
    ∃ T : ActualFlatDriftQuadraticStateFour N D.solution (D.drift 0) (D.source 0) (R*r) (a/2) M K,
      ‖fderiv ℝ T.polynomial 0-fderiv ℝ S.polynomial 0‖ ≤ a*R*K ∧
      ∀ x : E, ‖realHessian T.polynomial x-realHessian S.polynomial x‖ ≤ a*M := by
  have hSH : ‖realHessian S.polynomial 0‖ ≤ 2*M :=
    S.hessian.trans (by nlinarith [mul_nonneg hM.le ha.le])
  have hSD : ‖fderiv ℝ S.polynomial 0‖ ≤ 2*K :=
    S.gradient.trans (by nlinarith [mul_nonneg hK.le ha.le])
  let B : ActualFlatDriftPerturbationDataFour N lam Lambda delta :=
    actualFlatDriftResidualDataFour halpha halpha1 hk hR hR1 ha hRa
    (show 0 ≤ 2*M by positivity) (show 0 ≤ 2*K by positivity)
    (by nlinarith only [hsmall]) D S.quadratic S.zero hSH hSD S.frozen S.error
  have hbc : ContinuousOn B.drift (actualFlatClosedUpperBallFour N 1) :=
    (D.drift_continuous.comp (by fun_prop) (actual_flat_closed_unit_dilation_maps_four N hR hR1)).const_smul R
  have hfc : ContinuousOn B.source (actualFlatClosedUpperBallFour N 1) :=
    actual_flat_drift_residual_continuous_four hR hR1 D.continuous D.drift_continuous D.source_continuous S.quadratic
  obtain ⟨p,hp,hp0,hpt,hpD,hpH,herr⟩ := hstep B hbc hfc
  have hpfreeze : (realBlockHessian realDirections imagDirections p 0).trace+
      fderiv ℝ p 0 (R • D.drift 0) = 0 := by
    change (realBlockHessian realDirections imagDirections p 0).trace+
      fderiv ℝ p 0 (R • D.drift (R • (0 : E))) =
      -actualFlatDriftResidualSourceFour D.coeff.a D.drift D.source S.polynomial R a 0 at hpt
    rw [smul_zero,actual_flat_drift_residual_source_zero_four
      (actual_flat_drift_input_frozen_four hN halpha D) S.frozen,neg_zero] at hpt
    exact hpt
  have hnextH : ‖realHessian (scalarQuadraticUpdateTwo S.polynomial p R a) 0‖ ≤ 2*M*(1-a/2) := by
    rw [scalarQuadraticUpdateTwo_realHessian S.quadratic hp hR]
    calc
      _ ≤ ‖realHessian S.polynomial 0‖+‖a • realHessian p (R⁻¹ • (0 : E))‖ :=
        norm_add_le (realHessian S.polynomial (0 : E)) (a • realHessian p (R⁻¹ • (0 : E)))
      _ = ‖realHessian S.polynomial 0‖+a*‖realHessian p 0‖ := by
        rw [smul_zero,norm_smul,Real.norm_eq_abs,abs_of_pos ha]
      _ ≤ 2*M*(1-a)+a*M := add_le_add S.hessian (mul_le_mul_of_nonneg_left (hpH 0) ha.le)
      _ = _ := by ring
  let T : ActualFlatDriftQuadraticStateFour N D.solution (D.drift 0) (D.source 0) (R*r) (a/2) M K := {
    polynomial := scalarQuadraticUpdateTwo S.polynomial p R a
    quadratic := scalarQuadraticUpdateTwo_isQuadratic S.quadratic hp R a
    zero := actual_flat_quadratic_update_zero_four hR S.zero hp0
    frozen := actual_flat_drift_quadratic_update_frozen_four S.quadratic hp hR _ _ S.frozen hpfreeze
    gradient := actual_flat_drift_quadratic_update_gradient_bound_four S.quadratic hp hR hR1 ha hK.le S.gradient hpD
    hessian := hnextH
    error := actual_flat_quadratic_update_error_four hR ha herr
  }
  refine ⟨T,?_,?_⟩
  · change ‖fderiv ℝ (scalarQuadraticUpdateTwo S.polynomial p R a) 0-fderiv ℝ S.polynomial 0‖ ≤ a*R*K
    rw [(scalarQuadraticUpdateTwo_jet_increments S.quadratic hp hR).2.1,norm_smul,
      Real.norm_eq_abs,abs_of_pos (mul_pos ha hR)]
    exact mul_le_mul_of_nonneg_left hpD (mul_pos ha hR).le
  · intro x
    change ‖realHessian (scalarQuadraticUpdateTwo S.polynomial p R a) x-realHessian S.polynomial x‖ ≤ a*M
    rw [(scalarQuadraticUpdateTwo_jet_increments S.quadratic hp hR).2.2 x,
      norm_smul,Real.norm_eq_abs,abs_of_pos ha]
    exact mul_le_mul_of_nonneg_left (hpH 0) ha.le

end PowerConvexity
