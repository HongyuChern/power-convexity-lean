import PowerConvexity.Analysis.ActualPositiveMatrixFactorizationTwo
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-! # Actual invertible coordinates normalizing a positive frozen matrix. -/
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

def actualMatrixContinuousLinearEquivTwo (P : Mat) (hP : IsUnit P.det) : E ≃L[ℝ] E :=
  (Matrix.toLinearEquiv (PiLp.basisFun 2 ℝ (Fin (2+2))) P hP).toContinuousLinearEquiv

theorem actual_matrix_continuous_equiv_apply_two (P : Mat) (hP : IsUnit P.det) (v : E) :
    actualMatrixContinuousLinearEquivTwo P hP v = matMulE P v := by
  rfl

theorem actual_matrix_of_continuous_equiv_two (P : Mat) (hP : IsUnit P.det) :
    actualLinearMatrixTwo (actualMatrixContinuousLinearEquivTwo P hP) = P := by
  apply actual_matMulE_ext_two
  intro v
  rw [actual_linear_matrix_action_two,actual_matrix_continuous_equiv_apply_two]

theorem actual_positive_frozen_normalization_two {A : Mat} (hA : A.PosDef) :
    ∃ G : E ≃L[ℝ] E, actualLinearCongruenceMatrixTwo G A = 1 := by
  obtain ⟨P,hP,hAP⟩ := actual_positive_matrix_factorization_two hA
  let G := actualMatrixContinuousLinearEquivTwo P hP
  have hM : actualLinearMatrixTwo G = P := actual_matrix_of_continuous_equiv_two P hP
  refine ⟨G,?_⟩
  rw [actualLinearCongruenceMatrixTwo,← actual_linear_matrix_inverse_two,hM,hAP]
  calc
    P⁻¹*(P*Pᵀ)*P⁻¹ᵀ = (P⁻¹*P)*(Pᵀ*P⁻¹ᵀ) := by simp only [Matrix.mul_assoc]
    _ = 1 := by
      rw [Matrix.nonsing_inv_mul P hP,Matrix.transpose_nonsing_inv,
        Matrix.mul_nonsing_inv Pᵀ (Matrix.isUnit_det_transpose P hP),Matrix.one_mul]

end PowerConvexity
