import PowerConvexity.Analysis.ActualGraphShearFour

/-! # The second differential and curvature drift of a genuine graph shear -/
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

theorem actual_graph_shear_second_derivative_four {N x : E} {rho : E → ℝ}
    (hrho : ContDiffAt ℝ 2 rho x) (v w : E) :
    fderiv ℝ (fderiv ℝ (actualGraphShearFour N rho)) x v w =
      realHessian rho x v w • N := by
  let S : (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] E) := (ContinuousLinearMap.smulRightL ℝ E E).flip N
  have heq : fderiv ℝ (actualGraphShearFour N rho) =ᶠ[𝓝 x]
      (fun y => ContinuousLinearMap.id ℝ E+S (fderiv ℝ rho y)) := by
    filter_upwards [(hrho.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)).eventually (by norm_num)] with y hy
    exact (actual_graph_shear_hasFDerivAt_four (hy.differentiableAt (by norm_num))).fderiv
  have hd := ((hrho.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hc := (S.hasFDerivAt.comp x hd).const_add (ContinuousLinearMap.id ℝ E)
  have hh := heq.fderiv_eq (𝕜 := ℝ)
  have hh := hh.trans (by simpa only [Function.comp_def] using hc.fderiv)
  have hvw := congrArg (fun L : E →L[ℝ] E →L[ℝ] E => L v w) hh
  simpa only [S,realHessian,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.smulRightL_apply_apply,ContinuousLinearMap.smulRight_apply] using hvw

theorem actual_graph_shear_drift_four {N x : E} {rho : E → ℝ} (A : Mat)
    (hrho : ContDiffAt ℝ 2 rho x) (hN : fderiv ℝ rho x N = 0) :
    actualNonlinearChartDriftFour (actualShearLinearEquivFour N (fderiv ℝ rho x) hN) A
      (fderiv ℝ (fderiv ℝ (actualGraphShearFour N rho)) x) =
      -(∑ i, ∑ j, actualLinearCongruenceMatrixTwo
          (actualShearLinearEquivFour N (fderiv ℝ rho x) hN) A i j * euclideanHessian rho x i j) • N := by
  simp only [actualNonlinearChartDriftFour,actualNonlinearChartCurvatureFour,
    actual_graph_shear_second_derivative_four hrho,smul_smul]
  simp_rw [← Finset.sum_smul]
  rw [actual_shear_linear_inverse_four]
  simp only [map_smul,hN,smul_zero,zero_smul,sub_zero,neg_smul,euclideanHessian]

theorem actual_graph_shear_equation_four {N x : E} {rho u f : E → ℝ} (A : Mat)
    (hrho : ContDiffAt ℝ 2 rho x) (hN : fderiv ℝ rho x N = 0)
    (hu : ContDiffAt ℝ 2 u (actualGraphShearFour N rho x))
    (heq : (∑ i, ∑ j, A i j * euclideanHessian u (actualGraphShearFour N rho x) i j) =
      -f (actualGraphShearFour N rho x)) :
    let G := actualShearLinearEquivFour N (fderiv ℝ rho x) hN
    (∑ i, ∑ j, actualLinearCongruenceMatrixTwo G A i j *
      euclideanHessian (u ∘ actualGraphShearFour N rho) x i j) -
      (∑ i, ∑ j, actualLinearCongruenceMatrixTwo G A i j * euclideanHessian rho x i j) *
        fderiv ℝ (u ∘ actualGraphShearFour N rho) x N = -f (actualGraphShearFour N rho x) := by
  dsimp only
  have hh := actual_nonlinear_chart_equation_four
    (actualShearLinearEquivFour N (fderiv ℝ rho x) hN) A hu
    (actual_graph_shear_contDiffAt_four hrho)
    (actual_graph_shear_fderiv_equiv_four (hrho.differentiableAt (by norm_num)) hN) heq
  rw [actual_graph_shear_drift_four A hrho hN] at hh
  simpa only [map_smul,smul_eq_mul,neg_mul,sub_eq_add_neg] using hh

end PowerConvexity
