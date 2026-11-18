import PowerConvexity.Analysis.ActualFlatIterationDataFour

/-! # One actual boundary quadratic iteration step, with a summable Hessian increment -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_flat_quadratic_update_error_four {N : E} {u q p : E → ℝ} {R b r : ℝ}
    (hR : 0 < R) (hb : 0 < b)
    (herr : ∀ x ∈ actualFlatClosedUpperBallFour N r,
      |normalizedScalarResidualTwo u q R b x-p x| ≤ (1/2 : ℝ)*r^2) :
    ∀ x ∈ actualFlatClosedUpperBallFour N (R*r),
      |u x-scalarQuadraticUpdateTwo q p R b x| ≤ (b/2)*(R*r)^2 := by
  intro x hx
  have hm : R⁻¹ • x ∈ actualFlatClosedUpperBallFour N r := by
    have hh := actual_flat_smul_closedUpperBall_four (inv_pos.mpr hR) hx
    simpa only [← mul_assoc,inv_mul_cancel₀ hR.ne',one_mul] using hh
  have he : u x-scalarQuadraticUpdateTwo q p R b x =
      (b*R^2)*(normalizedScalarResidualTwo u q R b (R⁻¹ • x)-p (R⁻¹ • x)) := by
    simp only [scalarQuadraticUpdateTwo,scalarQuadraticLiftTwo_apply hR.ne',
      normalizedScalarResidualTwo,smul_smul,mul_inv_cancel₀ hR.ne',one_smul]
    field_simp
    ring
  rw [he,abs_mul,abs_of_pos (mul_pos hb (sq_pos_of_pos hR))]
  exact (mul_le_mul_of_nonneg_left (herr _ hm) (by positivity : 0 ≤ b*R^2)).trans_eq (by ring)

theorem actual_flat_quadratic_iteration_step_four
    {N : E} {lam Lambda alpha kappa R b r M delta : ℝ}
    (halpha : 0 < alpha) (hkappa : 0 ≤ kappa) (hR : 0 < R) (hR1 : R ≤ 1)
    (hb : 0 < b) (hb1 : b ≤ 1) (hM : 0 < M) (hRa : R^alpha ≤ b)
    (hsmall : kappa*(1+32*M) ≤ delta) (hd1 : delta ≤ 1)
    (D : ActualFlatIterationInputFour N lam Lambda alpha kappa)
    (hstep : ∀ B : ActualFlatPerturbationDataFour N lam Lambda 1 1 alpha delta,
      ∃ p : E → ℝ, IsQuadraticPolynomial p ∧
        (∀ x : E, inner ℝ N x=0 → p x=0) ∧
        (∀ x, (realBlockHessian realDirections imagDirections p x).trace=0) ∧
        (∀ x, ‖realHessian p x‖ ≤ M) ∧
        ∀ x ∈ actualFlatClosedUpperBallFour N r, |B.solution x-p x| ≤ (1/2 : ℝ)*r^2)
    (S : ActualFlatQuadraticStateFour N D.solution R b M) :
    ∃ T : ActualFlatQuadraticStateFour N D.solution (R*r) (b/2) M,
      ∀ x : E, ‖realHessian T.polynomial x-realHessian S.polynomial x‖ ≤ b*M := by
  have hSH : ‖realHessian S.polynomial 0‖ ≤ 2*M :=
    S.hessian.trans (by nlinarith [mul_nonneg hM.le hb.le])
  let B := actualFlatResidualDataFour halpha hkappa hR hR1 hb hb1
    (show 0 ≤ 2*M by positivity) hRa (by nlinarith only [hsmall]) hd1 D
    S.quadratic S.zero S.trace hSH S.error
  obtain ⟨p,hp,hp0,hpt,hpH,herr⟩ := hstep B
  have hnextH : ‖realHessian (scalarQuadraticUpdateTwo S.polynomial p R b) 0‖ ≤
      2*M*(1-b/2) := by
    rw [scalarQuadraticUpdateTwo_realHessian S.quadratic hp hR]
    calc
      _ ≤ ‖realHessian S.polynomial 0‖+‖b • realHessian p (R⁻¹ • (0 : E))‖ :=
        norm_add_le (realHessian S.polynomial (0 : E)) (b • realHessian p (R⁻¹ • (0 : E)))
      _ = ‖realHessian S.polynomial 0‖+b*‖realHessian p 0‖ := by
        rw [smul_zero,norm_smul,Real.norm_eq_abs,abs_of_pos hb]
      _ ≤ 2*M*(1-b)+b*M := add_le_add S.hessian (mul_le_mul_of_nonneg_left (hpH 0) hb.le)
      _ = _ := by ring
  let T : ActualFlatQuadraticStateFour N D.solution (R*r) (b/2) M := {
    polynomial := scalarQuadraticUpdateTwo S.polynomial p R b
    quadratic := scalarQuadraticUpdateTwo_isQuadratic S.quadratic hp R b
    zero := actual_flat_quadratic_update_zero_four hR S.zero hp0
    trace := scalarQuadraticUpdateTwo_trace_zero S.quadratic hp hR S.trace hpt
    hessian := hnextH
    error := actual_flat_quadratic_update_error_four hR hb herr
  }
  refine ⟨T,?_⟩
  intro x
  change ‖realHessian (scalarQuadraticUpdateTwo S.polynomial p R b) x-
    realHessian S.polynomial x‖ ≤ b*M
  rw [(scalarQuadraticUpdateTwo_jet_increments S.quadratic hp hR).2.2 x,
    norm_smul,Real.norm_eq_abs,abs_of_pos hb]
  exact mul_le_mul_of_nonneg_left (hpH 0) hb.le

end PowerConvexity
