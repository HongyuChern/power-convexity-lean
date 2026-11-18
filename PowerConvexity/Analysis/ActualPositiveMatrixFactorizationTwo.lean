import PowerConvexity.Analysis.ActualLinearCoefficientCongruenceTwo
import Mathlib.Analysis.Matrix.PosDef

/-! # Actual positive definite matrix factorization.
The factor is constructed from the locked spectral theorem and positive
square roots of the actual eigenvalues. Its determinant is proved a unit.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
local notation "Mat" => Matrix (Fin (2+2)) (Fin (2+2)) ℝ
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_positive_matrix_factorization_two {A : Mat} (hA : A.PosDef) :
    ∃ P : Mat, IsUnit P.det ∧ A = P*Pᵀ := by
  let U := hA.isHermitian.eigenvectorUnitary
  let D : Mat := Matrix.diagonal (fun i => Real.sqrt (hA.isHermitian.eigenvalues i))
  have hD : 0 < D.det := by
    change 0 < (Matrix.diagonal (fun i => Real.sqrt (hA.isHermitian.eigenvalues i))).det
    rw [Matrix.det_diagonal]
    exact Finset.prod_pos (fun i hi => Real.sqrt_pos.mpr (hA.eigenvalues_pos i))
  have hU : IsUnit (U : Mat).det := (Matrix.isUnit_iff_isUnit_det _).mp Unitary.isUnit_coe
  have hDD : D*D = Matrix.diagonal hA.isHermitian.eigenvalues := by
    change Matrix.diagonal (fun i => Real.sqrt (hA.isHermitian.eigenvalues i))*
      Matrix.diagonal (fun i => Real.sqrt (hA.isHermitian.eigenvalues i)) = _
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact Real.mul_self_sqrt (hA.eigenvalues_pos i).le
  have hDt : Dᵀ = D := Matrix.diagonal_transpose _
  have hspec : A = (U : Mat)*Matrix.diagonal hA.isHermitian.eigenvalues*(U : Mat)ᵀ := by
    simpa [U,Unitary.conjStarAlgAut_apply,Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using
      hA.isHermitian.spectral_theorem
  refine ⟨(U : Mat)*D,?_,?_⟩
  · rw [Matrix.det_mul]
    exact hU.mul (isUnit_iff_ne_zero.mpr hD.ne')
  · rw [Matrix.transpose_mul,hDt]
    calc
      A = (U : Mat)*Matrix.diagonal hA.isHermitian.eigenvalues*(U : Mat)ᵀ := hspec
      _ = ((U : Mat)*D)*(D*(U : Mat)ᵀ) := by rw [← hDD]; simp only [Matrix.mul_assoc]

end PowerConvexity
