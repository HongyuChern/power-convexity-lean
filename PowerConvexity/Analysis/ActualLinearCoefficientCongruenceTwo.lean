import PowerConvexity.Analysis.ActualScalarLinearPullbackTwo

/-! # Actual matrix congruence for linear changes of variables. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
local notation "Mat" => Matrix (Fin (2+2)) (Fin (2+2)) ℝ
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

def actualLinearMatrixTwo (G : E ≃L[ℝ] E) : Mat :=
  Matrix.toEuclideanLin.symm G.toLinearMap

theorem actual_linear_matrix_action_two (G : E ≃L[ℝ] E) (v : E) :
    matMulE (actualLinearMatrixTwo G) v = G v := by
  change Matrix.toEuclideanLin (Matrix.toEuclideanLin.symm G.toLinearMap) v = G v
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem actual_linear_matrix_entry_two (G : E ≃L[ℝ] E) (i j : Fin (2+2)) :
    actualLinearMatrixTwo G i j = (G (EuclideanSpace.single j 1)) i := by
  have hh := congrArg (fun v : E => v i)
    (actual_linear_matrix_action_two G (EuclideanSpace.single j 1))
  simpa only [matMulE_apply,PiLp.ofLp_single,Matrix.mulVec_single_one,Matrix.col_apply] using hh

theorem actual_matMulE_mul_two (A B : Mat) (v : E) :
    matMulE (A*B) v = matMulE A (matMulE B v) := by
  ext i
  simp only [matMulE_apply,matMulE_ofLp,Matrix.mulVec_mulVec]

theorem actual_matMulE_ext_two {A B : Mat} (h : ∀ v : E, matMulE A v = matMulE B v) : A = B := by
  ext i j
  have hh := congrArg (fun v : E => v i) (h (EuclideanSpace.single j 1))
  simpa only [matMulE_apply,PiLp.ofLp_single,Matrix.mulVec_single_one,Matrix.col_apply] using hh

theorem actual_linear_matrix_inverse_two (G : E ≃L[ℝ] E) :
    (actualLinearMatrixTwo G)⁻¹ = actualLinearMatrixTwo G.symm := by
  apply Matrix.inv_eq_left_inv
  apply actual_matMulE_ext_two
  intro v
  rw [actual_matMulE_mul_two,actual_linear_matrix_action_two,actual_linear_matrix_action_two]
  simp only [G.symm_apply_apply,matMulE,Matrix.one_mulVec,WithLp.toLp_ofLp]

theorem actual_linear_matrix_transpose_action_two (G : E ≃L[ℝ] E) (v : E) :
    matMulE (actualLinearMatrixTwo G)ᵀ v = G.toContinuousLinearMap.adjoint v := by
  rw [← actual_linear_weak_gradient_adjoint_two G (fun _ => v) 0]
  ext i
  simp only [matMulE_apply,Matrix.mulVec,Matrix.transpose_apply,dotProduct,
    actual_linear_matrix_entry_two,actualLinearWeakGradientTwo,PiLp.toLp_apply]

def actualLinearCongruenceMatrixTwo (G : E ≃L[ℝ] E) (A : Mat) : Mat :=
  actualLinearMatrixTwo G.symm*A*(actualLinearMatrixTwo G.symm)ᵀ

theorem actual_linear_congruence_action_two (G : E ≃L[ℝ] E) (A : Mat) (v : E) :
    matMulE (actualLinearCongruenceMatrixTwo G A) v =
      G.symm (matMulE A (G.symm.toContinuousLinearMap.adjoint v)) := by
  rw [actualLinearCongruenceMatrixTwo,actual_matMulE_mul_two,actual_matMulE_mul_two,
    actual_linear_matrix_action_two,actual_linear_matrix_transpose_action_two]

theorem actual_linear_congruence_inverse_two (G : E ≃L[ℝ] E) (A : Mat) :
    (actualLinearCongruenceMatrixTwo G A)⁻¹ =
      (actualLinearMatrixTwo G)ᵀ*A⁻¹*actualLinearMatrixTwo G := by
  simp only [actualLinearCongruenceMatrixTwo,Matrix.mul_inv_rev,
    ← Matrix.transpose_nonsing_inv,actual_linear_matrix_inverse_two,G.symm_symm]
  rw [Matrix.mul_assoc]

theorem actual_linear_congruence_inverse_action_two (G : E ≃L[ℝ] E) (A : Mat) (v : E) :
    matMulE (actualLinearCongruenceMatrixTwo G A)⁻¹ v =
      G.toContinuousLinearMap.adjoint (matMulE A⁻¹ (G v)) := by
  rw [actual_linear_congruence_inverse_two,actual_matMulE_mul_two,actual_matMulE_mul_two,
    actual_linear_matrix_transpose_action_two,actual_linear_matrix_action_two]

theorem actual_linear_congruence_measurable_two (G : E ≃L[ℝ] E)
    {A : E → Mat} (hA : ∀ i j, Measurable (fun x => A x i j)) (i j : Fin (2+2)) :
    Measurable (fun z => actualLinearCongruenceMatrixTwo G (A (G z)) i j) := by
  simp only [actualLinearCongruenceMatrixTwo,Matrix.mul_apply]
  exact Finset.measurable_sum _ (fun k hk =>
    (Finset.measurable_sum _ (fun l hl => measurable_const.mul
      ((hA l k).comp G.continuous.measurable))).mul measurable_const)

end PowerConvexity
