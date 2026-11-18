import PowerConvexity.Analysis.ActualGraphShearHessianFour

/-! # One actual coefficient field for the nonlinear graph chart -/
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

def actualShearInverseMatrixFour (N : E) (l : E →L[ℝ] ℝ) : Mat :=
  Matrix.of (fun i j => (1 : Mat) i j-N i*l (EuclideanSpace.single j 1))

def actualGraphShearCoefficientFour (N : E) (rho : E → ℝ) (a : E → Mat) (x : E) : Mat :=
  actualShearInverseMatrixFour N (fderiv ℝ rho x) * a (actualGraphShearFour N rho x) *
    (actualShearInverseMatrixFour N (fderiv ℝ rho x))ᵀ

theorem actual_shear_inverse_matrix_four (N : E) (l : E →L[ℝ] ℝ) (hl : l N = 0) :
    actualShearInverseMatrixFour N l = actualLinearMatrixTwo (actualShearLinearEquivFour N l hl).symm := by
  ext i j
  rw [actual_linear_matrix_entry_two,actual_shear_linear_inverse_four]
  simp only [actualShearInverseMatrixFour,Matrix.of_apply,PiLp.sub_apply,PiLp.smul_apply,
    smul_eq_mul,EuclideanSpace.single_apply,Matrix.one_apply]
  ring

theorem actual_graph_shear_coefficient_congruence_four {N x : E} {rho : E → ℝ}
    (a : E → Mat) (hN : fderiv ℝ rho x N = 0) :
    actualGraphShearCoefficientFour N rho a x =
      actualLinearCongruenceMatrixTwo (actualShearLinearEquivFour N (fderiv ℝ rho x) hN)
        (a (actualGraphShearFour N rho x)) := by
  simp only [actualGraphShearCoefficientFour,actual_shear_inverse_matrix_four N _ hN,
    actualLinearCongruenceMatrixTwo]

theorem actual_graph_shear_coefficient_regular_four {U V : Set E} (hV : IsOpen V)
    {N : E} {rho : E → ℝ} {a : E → Mat}
    (hrho : ContDiffOn ℝ 2 rho V)
    (ha : ∀ i j, ContDiffOn ℝ 1 (fun y => a y i j) U)
    (hmap : MapsTo (actualGraphShearFour N rho) V U) (i j : Fin (2+2)) :
    ContDiffOn ℝ 1 (fun x => actualGraphShearCoefficientFour N rho a x i j) V := by
  have hD := hrho.fderiv_of_isOpen hV (m := 1) (by norm_num)
  have hQ (k l : Fin (2+2)) :
      ContDiffOn ℝ 1 (fun x => actualShearInverseMatrixFour N (fderiv ℝ rho x) k l) V :=
    contDiffOn_const.sub (contDiffOn_const.mul (hD.clm_apply contDiffOn_const))
  have hPhi : ContDiffOn ℝ 1 (actualGraphShearFour N rho) V :=
    contDiffOn_id.add ((hrho.of_le (by norm_num)).smul contDiffOn_const)
  simp only [actualGraphShearCoefficientFour,Matrix.mul_apply,Matrix.transpose_apply]
  apply ContDiffOn.sum
  intro k _
  apply ContDiffOn.mul _ (hQ j k)
  apply ContDiffOn.sum
  intro l _
  exact (hQ i l).mul ((ha l k).comp hPhi hmap)

theorem actual_shear_inverse_matrix_fderiv_four {N x : E} {rho : E → ℝ}
    (hrho : ContDiffAt ℝ 2 rho x) (i j : Fin (2+2)) (v : E) :
    fderiv ℝ (fun y => actualShearInverseMatrixFour N (fderiv ℝ rho y) i j) x v =
      -N i * realHessian rho x v (EuclideanSpace.single j 1) := by
  have hD := ((hrho.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have he := hD.clm_apply (hasFDerivAt_const (EuclideanSpace.single j (1 : ℝ) : E) x)
  have hh := (hasFDerivAt_const ((1 : Mat) i j) x).sub (he.const_mul (N i))
  have hv := congrArg (fun L : E →L[ℝ] ℝ => L v) hh.fderiv
  have heq : (fun y => actualShearInverseMatrixFour N (fderiv ℝ rho y) i j) =
      ((fun _ : E => (1 : Mat) i j) - (fun y => N i * fderiv ℝ rho y (EuclideanSpace.single j 1))) := by
    funext y
    rfl
  rw [heq]
  simpa only [realHessian,
    Pi.sub_apply,_root_.sub_apply,_root_.add_apply,_root_.smul_apply,_root_.neg_apply,ContinuousLinearMap.comp_zero,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply,ContinuousLinearMap.flip_apply,smul_eq_mul,
    map_zero,zero_add,zero_sub,neg_mul] using hv

theorem actual_graph_shear_coefficient_frozen_four {N x : E} {rho : E → ℝ} {a : E → Mat}
    (hrho : rho x = 0) (hD : fderiv ℝ rho x = 0) :
    actualGraphShearCoefficientFour N rho a x = a x := by
  have hQ : actualShearInverseMatrixFour N (fderiv ℝ rho x) = 1 := by
    ext i j
    simp only [actualShearInverseMatrixFour,hD,ContinuousLinearMap.zero_apply,mul_zero,sub_zero,Matrix.of_apply]
  simp only [actualGraphShearCoefficientFour,hQ,actualGraphShearFour,hrho,zero_smul,add_zero,
    Matrix.transpose_one,Matrix.one_mul,Matrix.mul_one]

end PowerConvexity
