import PowerConvexity.Analysis.ActualGraphShearAlgebraFour

/-! # Entry derivatives of the same genuine graph-chart coefficient -/
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

theorem actual_graph_shear_coefficient_fderiv_four {N x : E} {rho : E → ℝ} {a : E → Mat}
    (hrho : ContDiffAt ℝ 2 rho x)
    (ha : ∀ i j, DifferentiableAt ℝ (fun y => a y i j) (actualGraphShearFour N rho x))
    (i j : Fin (2+2)) (v : E) :
    let Q := actualShearInverseMatrixFour N (fderiv ℝ rho x)
    fderiv ℝ (fun y => actualGraphShearCoefficientFour N rho a y i j) x v =
      ∑ k, ∑ l, (
        (-N i*realHessian rho x v (EuclideanSpace.single l 1))*a (actualGraphShearFour N rho x) l k*Q j k +
        Q i l*fderiv ℝ (fun y => a y l k) (actualGraphShearFour N rho x)
          (fderiv ℝ (actualGraphShearFour N rho) x v)*Q j k +
        Q i l*a (actualGraphShearFour N rho x) l k*(-N j*realHessian rho x v (EuclideanSpace.single k 1))) := by
  dsimp only
  let Q : E → Mat := fun y => actualShearInverseMatrixFour N (fderiv ℝ rho y)
  let Phi := actualGraphShearFour N rho
  have hQ (k l : Fin (2+2)) : DifferentiableAt ℝ (fun y => Q y k l) x := by
    have hqc : ContDiffAt ℝ 1 (fun y => Q y k l) x :=
      contDiffAt_const.sub (contDiffAt_const.mul
        ((hrho.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const))
    exact hqc.differentiableAt (by norm_num)
  have hPhi : DifferentiableAt ℝ Phi x :=
    (actual_graph_shear_contDiffAt_four hrho).differentiableAt (by norm_num)
  have hA (k l : Fin (2+2)) := (ha k l).hasFDerivAt.comp x hPhi.hasFDerivAt
  have hterm (k l : Fin (2+2)) :=
    (((hQ i l).hasFDerivAt.mul (hA l k)).mul (hQ j k).hasFDerivAt)
  have hd := HasFDerivAt.fun_sum (u := Finset.univ) (fun k _ =>
    HasFDerivAt.fun_sum (u := Finset.univ) (fun l _ => hterm k l))
  have heq : (fun y => actualGraphShearCoefficientFour N rho a y i j) =
      (fun y => ∑ k, ∑ l, Q y i l*a (Phi y) l k*Q y j k) := by
    funext y
    simp only [actualGraphShearCoefficientFour,Matrix.mul_apply,Matrix.transpose_apply,Finset.sum_mul,Q,Phi]
  rw [heq]
  simp only [Pi.mul_apply,Function.comp_def] at hd
  have hv := congrArg (fun L : E →L[ℝ] ℝ => L v) hd.fderiv
  simp only [Pi.mul_apply,Function.comp_def,_root_.sum_apply,_root_.add_apply,_root_.smul_apply,smul_eq_mul,
    ContinuousLinearMap.comp_apply] at hv
  rw [hv]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  simp only [Q,Phi,actual_shear_inverse_matrix_fderiv_four hrho]
  ring

end PowerConvexity
