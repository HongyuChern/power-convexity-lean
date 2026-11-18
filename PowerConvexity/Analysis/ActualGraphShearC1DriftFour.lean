import PowerConvexity.Analysis.ActualGraphShearPhysicalScaleFour
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! # C1 regularity of the same actual chart coefficient and generated drift -/
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

theorem actual_graph_shear_coefficient_contDiffAt_four {N x : E} {rho : E → ℝ} {a : E → Mat}
    (hrho : ContDiffAt ℝ 2 rho x)
    (ha : ∀ i j, ContDiffAt ℝ 1 (fun y => a y i j) (actualGraphShearFour N rho x)) :
    ContDiffAt ℝ 1 (actualGraphShearCoefficientFour N rho a) x := by
  have hD := hrho.fderiv_right (m := 1) (by norm_num)
  have hQ (i j : Fin (2+2)) : ContDiffAt ℝ 1
      (fun y => actualShearInverseMatrixFour N (fderiv ℝ rho y) i j) x :=
    contDiffAt_const.sub (contDiffAt_const.mul (hD.clm_apply contDiffAt_const))
  have hPhi := (actual_graph_shear_contDiffAt_four (N := N) hrho).of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  change ContDiffAt ℝ 1 (fun y => actualGraphShearCoefficientFour N rho a y i j) x
  simp only [actualGraphShearCoefficientFour,Matrix.mul_apply,Matrix.transpose_apply]
  apply ContDiffAt.sum
  intro k _
  apply ContDiffAt.mul _ (hQ j k)
  apply ContDiffAt.sum
  intro l _
  exact (hQ i l).mul ((ha l k).comp x hPhi)

theorem actual_graph_shear_drift_field_contDiffAt_four {N x : E} {rho : E → ℝ} {a : E → Mat}
    (hrho : ContDiffAt ℝ 3 rho x)
    (ha : ∀ i j, ContDiffAt ℝ 1 (fun y => a y i j) (actualGraphShearFour N rho x)) :
    ContDiffAt ℝ 1 (actualGraphShearDriftFieldFour N rho a) x := by
  have hH : ContDiffAt ℝ 1 (realHessian rho) x :=
    (hrho.fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)
  have hPhi := (actual_graph_shear_contDiffAt_four (N := N) hrho).of_le (by norm_num : (1 : ℕ∞ω) ≤ 3)
  change ContDiffAt ℝ 1 ((fun y => -(∑ k, ∑ l,
    a (actualGraphShearFour N rho y) l k*euclideanHessian rho y l k)) • (fun _ : E => N)) x
  apply ContDiffAt.smul _ contDiffAt_const
  apply ContDiffAt.neg
  apply ContDiffAt.sum
  intro k _
  apply ContDiffAt.sum
  intro l _
  exact ((ha l k).comp x hPhi).mul ((hH.clm_apply contDiffAt_const).clm_apply contDiffAt_const)

end PowerConvexity
