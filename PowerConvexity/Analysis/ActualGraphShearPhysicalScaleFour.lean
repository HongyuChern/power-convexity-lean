import PowerConvexity.Analysis.ActualSmallScaleDriftFour

/-! # Simultaneous principal-part and drift control in the same chart -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace Matrix.Norms.Elementwise
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
local notation "Mat" => Matrix (Fin (2+2)) (Fin (2+2)) ℝ
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_graph_shear_coefficient_continuousAt_four {N x : E} {rho : E → ℝ} {a : E → Mat}
    (hrho : ContDiffAt ℝ 2 rho x)
    (ha : ∀ i j, ContinuousAt (fun y => a y i j) (actualGraphShearFour N rho x)) :
    ContinuousAt (actualGraphShearCoefficientFour N rho a) x := by
  have hD := (hrho.fderiv_right (m := 1) (by norm_num)).continuousAt
  have hQ (i j : Fin (2+2)) : ContinuousAt
      (fun y => actualShearInverseMatrixFour N (fderiv ℝ rho y) i j) x :=
    continuousAt_const.sub (continuousAt_const.mul (hD.clm_apply continuousAt_const))
  have hPhi := (actual_graph_shear_contDiffAt_four (N := N) hrho).continuousAt
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro j
  change ContinuousAt (fun y => actualGraphShearCoefficientFour N rho a y i j) x
  simp only [actualGraphShearCoefficientFour,Matrix.mul_apply,Matrix.transpose_apply]
  apply tendsto_finsetSum
  intro k _
  apply ContinuousAt.mul _ (hQ j k)
  apply tendsto_finsetSum
  intro l _
  exact (hQ i l).mul ((ha l k).comp hPhi)

theorem actual_graph_shear_normalized_physical_scale_four {N : E} {rho : E → ℝ} {a : E → Mat}
    (hrho : ContDiffAt ℝ 2 rho 0) (hrho0 : rho 0=0) (hD0 : fderiv ℝ rho 0=0)
    (ha : ∀ i j, ContinuousAt (fun y => a y i j) 0) (ha0 : a 0=1)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ r > 0, r ≤ 1 ∧ ∀ z : E, ‖z‖ ≤ 1 →
      ‖actualMatrixOperatorTwo (actualGraphShearCoefficientFour N rho a (r • z))-
        ContinuousLinearMap.id ℝ E‖ ≤ delta ∧
      r*‖actualGraphShearDriftFieldFour N rho a (r • z)‖ ≤ delta := by
  have hPhi0 : actualGraphShearFour N rho 0=0 := by
    simp only [actualGraphShearFour,hrho0,zero_smul,add_zero]
  have ha' (i j : Fin (2+2)) : ContinuousAt (fun y => a y i j) (actualGraphShearFour N rho 0) := by
    simpa only [hPhi0] using ha i j
  have hB := actual_graph_shear_coefficient_continuousAt_four (N := N) hrho ha'
  have hBO : ContinuousAt (fun y => actualMatrixOperatorTwo (actualGraphShearCoefficientFour N rho a y)) 0 :=
    actualMatrixOperatorTwo.continuous.continuousAt.comp hB
  have hBI : actualMatrixOperatorTwo (actualGraphShearCoefficientFour N rho a 0) = ContinuousLinearMap.id ℝ E := by
    rw [actual_graph_shear_coefficient_frozen_four hrho0 hD0,ha0,actual_matrix_operator_one_two]
  exact actual_small_scale_operator_drift_four hBO hBI
    (actual_graph_shear_drift_field_continuousAt_four hrho ha') hdelta

theorem actual_graph_shear_columns_eq_drift_field_four {N x : E} {rho : E → ℝ} {a : E → Mat}
    (hrho : ContDiffAt ℝ 2 rho x)
    (hNrho : ∀ᶠ y in 𝓝 x, fderiv ℝ rho y N=0)
    (ha : ∀ i j, DifferentiableAt ℝ (fun y => a y i j) (actualGraphShearFour N rho x))
    (hdiv : ∀ j, (∑ i, fderiv ℝ (fun y => a y i j) (actualGraphShearFour N rho x)
      (EuclideanSpace.single i 1))=0) :
    actualCoefficientColumnDivergenceFour (actualGraphShearCoefficientFour N rho a) x =
      actualGraphShearDriftFieldFour N rho a x := by
  ext j
  change (∑ i, fderiv ℝ (fun y => actualGraphShearCoefficientFour N rho a y i j) x
    (EuclideanSpace.single i 1)) = (actualGraphShearDriftFieldFour N rho a x) j
  rw [actual_graph_shear_column_divergence_four hrho hNrho ha j]
  simp only [hdiv,mul_zero,Finset.sum_const_zero,zero_sub,actualGraphShearDriftFieldFour,
    PiLp.smul_apply,smul_eq_mul]
  ring

end PowerConvexity
