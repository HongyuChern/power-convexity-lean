import PowerConvexity.Analysis.ActualGraphShearDivergenceFour
import PowerConvexity.Analysis.ActualLocalClassicalDriftWeakFour

/-! # The generated column divergence is exactly the actual chart drift -/
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

theorem actual_graph_shear_divergence_equals_drift_four {N x : E} {rho : E → ℝ} {a : E → Mat}
    (hrho : ContDiffAt ℝ 2 rho x)
    (hNrho : ∀ᶠ y in 𝓝 x, fderiv ℝ rho y N = 0)
    (ha : ∀ i j, DifferentiableAt ℝ (fun y => a y i j) (actualGraphShearFour N rho x))
    (hdiv : ∀ j, (∑ i, fderiv ℝ (fun y => a y i j) (actualGraphShearFour N rho x)
      (EuclideanSpace.single i 1))=0) :
    let hN := hNrho.self_of_nhds
    let G := actualShearLinearEquivFour N (fderiv ℝ rho x) hN
    actualCoefficientColumnDivergenceFour (actualGraphShearCoefficientFour N rho a) x =
      actualNonlinearChartDriftFour G (a (actualGraphShearFour N rho x))
        (fderiv ℝ (fderiv ℝ (actualGraphShearFour N rho)) x) := by
  dsimp only
  have hN : fderiv ℝ rho x N=0 := hNrho.self_of_nhds
  have hc := actual_shear_tangential_contraction_four N (fderiv ℝ rho x) hN
    (a (actualGraphShearFour N rho x)) (realHessian rho x)
    (fun v w => realHessian_symm hrho v w)
    (fun v => actual_normal_hessian_vanishes_four hrho hNrho v)
  change (∑ i, ∑ j, actualGraphShearCoefficientFour N rho a x i j*euclideanHessian rho x i j) =
    ∑ i, ∑ j, a (actualGraphShearFour N rho x) i j*euclideanHessian rho x i j at hc
  rw [actual_graph_shear_drift_four _ hrho hN]
  rw [← actual_graph_shear_coefficient_congruence_four a hN,hc]
  ext j
  change (∑ i, fderiv ℝ (fun y => actualGraphShearCoefficientFour N rho a y i j) x
    (EuclideanSpace.single i 1)) =
    (-(∑ i, ∑ k, a (actualGraphShearFour N rho x) i k*euclideanHessian rho x i k) • N) j
  rw [actual_graph_shear_column_divergence_four hrho hNrho ha j]
  simp only [hdiv,mul_zero,Finset.sum_const_zero,zero_sub,PiLp.smul_apply,smul_eq_mul]
  rw [Finset.sum_comm]
  ring

theorem actual_graph_shear_classical_flux_equation_four {N x : E} {rho u f : E → ℝ} {a : E → Mat}
    (hrho : ContDiffAt ℝ 2 rho x)
    (hNrho : ∀ᶠ y in 𝓝 x, fderiv ℝ rho y N = 0)
    (ha : ∀ i j, DifferentiableAt ℝ (fun y => a y i j) (actualGraphShearFour N rho x))
    (hdiv : ∀ j, (∑ i, fderiv ℝ (fun y => a y i j) (actualGraphShearFour N rho x)
      (EuclideanSpace.single i 1))=0)
    (hu : ContDiffAt ℝ 2 u (actualGraphShearFour N rho x))
    (heq : (∑ i, ∑ j, a (actualGraphShearFour N rho x) i j *
      euclideanHessian u (actualGraphShearFour N rho x) i j) = -f (actualGraphShearFour N rho x)) :
    classicalDivergence (fun y => matMulE (actualGraphShearCoefficientFour N rho a y)
      (smoothGradField (u ∘ actualGraphShearFour N rho) y)) x = -f (actualGraphShearFour N rho x) := by
  have hN : fderiv ℝ rho x N=0 := hNrho.self_of_nhds
  have hPhi := actual_graph_shear_contDiffAt_four (N := N) hrho
  have hB (i j : Fin (2+2)) : DifferentiableAt ℝ (fun y => actualGraphShearCoefficientFour N rho a y i j) x := by
    have hQ (k l : Fin (2+2)) : DifferentiableAt ℝ
        (fun y => actualShearInverseMatrixFour N (fderiv ℝ rho y) k l) x := by
      have hqc : ContDiffAt ℝ 1 (fun y => actualShearInverseMatrixFour N (fderiv ℝ rho y) k l) x :=
        contDiffAt_const.sub (contDiffAt_const.mul
          ((hrho.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const))
      exact hqc.differentiableAt (by norm_num)
    simp only [actualGraphShearCoefficientFour,Matrix.mul_apply,Matrix.transpose_apply]
    apply DifferentiableAt.fun_sum
    intro k _
    apply DifferentiableAt.mul _ (hQ j k)
    apply DifferentiableAt.fun_sum
    intro l _
    exact (hQ i l).mul ((ha l k).comp x (hPhi.differentiableAt (by norm_num)))
  rw [actual_classical_divergence_with_drift_four hB (hu.comp x hPhi),
    actual_graph_shear_divergence_equals_drift_four hrho hNrho ha hdiv]
  have hh := actual_nonlinear_chart_equation_four
    (actualShearLinearEquivFour N (fderiv ℝ rho x) hN) (a (actualGraphShearFour N rho x))
    hu hPhi (actual_graph_shear_fderiv_equiv_four (hrho.differentiableAt (by norm_num)) hN) heq
  simpa only [← actual_graph_shear_coefficient_congruence_four a hN,euclideanHessian] using hh

end PowerConvexity
