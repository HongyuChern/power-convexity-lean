import PowerConvexity.Analysis.ActualNonlinearChartHessianFour

/-! # The exact transformed operator, including the curvature drift -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
local notation "Mat" => Matrix (Fin (2+2)) (Fin (2+2)) ℝ
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_bilinear_congruence_contraction_four (G : E ≃L[ℝ] E) (A : Mat)
    (H : Bilin) (hH : ∀ v w, H v w = H w v) :
    (∑ i, ∑ j, actualLinearCongruenceMatrixTwo G A i j *
      H (G (EuclideanSpace.single i 1)) (G (EuclideanSpace.single j 1))) =
        ∑ i, ∑ j, A i j * H (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
  let M : Mat := Matrix.of (fun i j => H (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))
  have hleft : (∑ i, ∑ j, actualLinearCongruenceMatrixTwo G A i j *
      H (G (EuclideanSpace.single i 1)) (G (EuclideanSpace.single j 1))) =
      ((actualLinearCongruenceMatrixTwo G A) *
        ((actualLinearMatrixTwo G)ᵀ * M * actualLinearMatrixTwo G)).trace := by
    rw [← actual_bilinear_matrix_pullback_four G H]
    simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,Matrix.of_apply]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hH]
  have hright : (∑ i, ∑ j, A i j * H (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) =
      (A*M).trace := by
    simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,M,Matrix.of_apply]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hH]
  rw [hleft,actual_inverse_congruence_trace_cancellation_four,hright]

def actualNonlinearChartCurvatureFour (G : E ≃L[ℝ] E) (A : Mat)
    (D2 : E →L[ℝ] E →L[ℝ] E) : E :=
  ∑ i, ∑ j, actualLinearCongruenceMatrixTwo G A i j •
    D2 (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)

def actualNonlinearChartDriftFour (G : E ≃L[ℝ] E) (A : Mat)
    (D2 : E →L[ℝ] E →L[ℝ] E) : E := -G.symm (actualNonlinearChartCurvatureFour G A D2)

theorem actual_nonlinear_chart_contraction_four {u : E → ℝ} {Phi : E → E} {x : E}
    (G : E ≃L[ℝ] E) (A : Mat)
    (hu : ContDiffAt ℝ 2 u (Phi x)) (hPhi : ContDiffAt ℝ 2 Phi x)
    (hG : fderiv ℝ Phi x = G.toContinuousLinearMap) :
    (∑ i, ∑ j, actualLinearCongruenceMatrixTwo G A i j * euclideanHessian (u ∘ Phi) x i j) =
      (∑ i, ∑ j, A i j * euclideanHessian u (Phi x) i j) +
        fderiv ℝ u (Phi x) (actualNonlinearChartCurvatureFour G A (fderiv ℝ (fderiv ℝ Phi) x)) := by
  simp only [euclideanHessian,actual_nonlinear_chart_hessian_four hu hPhi,hG,
    ContinuousLinearEquiv.coe_coe,mul_add,Finset.sum_add_distrib]
  rw [actual_bilinear_congruence_contraction_four G A (realHessian u (Phi x))
    (fun v w => realHessian_symm hu v w)]
  congr 1
  simp only [actualNonlinearChartCurvatureFour,map_sum,map_smul,smul_eq_mul]

theorem actual_nonlinear_chart_equation_four {u f : E → ℝ} {Phi : E → E} {x : E}
    (G : E ≃L[ℝ] E) (A : Mat)
    (hu : ContDiffAt ℝ 2 u (Phi x)) (hPhi : ContDiffAt ℝ 2 Phi x)
    (hG : fderiv ℝ Phi x = G.toContinuousLinearMap)
    (heq : (∑ i, ∑ j, A i j * euclideanHessian u (Phi x) i j) = -f (Phi x)) :
    (∑ i, ∑ j, actualLinearCongruenceMatrixTwo G A i j * euclideanHessian (u ∘ Phi) x i j) +
      fderiv ℝ (u ∘ Phi) x (actualNonlinearChartDriftFour G A (fderiv ℝ (fderiv ℝ Phi) x)) =
        -f (Phi x) := by
  rw [actual_nonlinear_chart_contraction_four G A hu hPhi hG,heq,
    fderiv_comp x (hu.differentiableAt (by norm_num)) (hPhi.differentiableAt (by norm_num)),hG]
  simp only [actualNonlinearChartDriftFour,ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe,map_neg,G.apply_symm_apply]
  ring

end PowerConvexity
