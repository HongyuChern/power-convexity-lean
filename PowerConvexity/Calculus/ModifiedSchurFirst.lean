import PowerConvexity.Calculus.ConjugateContraction

/-! # The first modified Schur derivative and its normalized entry -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ContDiff Topology ComplexOrder

namespace PowerConvexity
open CHS.Calculus CHS.SchurContractionCore
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem matrixDZ_modifiedSchur {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 4 u x) (hx : u x < 0) (a b : ι → E)
    (hA : (complexHessian a b u x).PosDef) (p : ι) :
    matrixDZ (a p) (b p) (modifiedSchur a b u) x =
      matrixDZ (a p) (b p) (modifiedA a b u) x -
      modifiedCompensatedHessian a b u p x * ((modifiedA a b u x).map star)⁻¹ *
        (modifiedB a b u x).map star -
      modifiedB a b u x * ((modifiedA a b u x).map star)⁻¹ *
        matrixDZ (a p) (b p) (fun y => (modifiedB a b u y).map star) x := by
  have hAm := modifiedA_posDef a b hx hA
  have hH : (modifiedA a b u x).map star = (modifiedA a b u x).transpose := by
    ext i j
    exact hAm.isHermitian.apply j i
  have hdet : ((modifiedA a b u x).map star).det ≠ 0 := by
    rw [hH, Matrix.det_transpose]
    exact ne_of_gt hAm.det_pos
  have hAd : MatrixDifferentiableAt (modifiedA a b u) x :=
    fun i j => (modifiedA_contDiffAt_two hu hx a b i j).differentiableAt (by norm_num)
  have hBd : MatrixDifferentiableAt (modifiedB a b u) x :=
    fun i j => (modifiedB_contDiffAt_two hu hx a b i j).differentiableAt (by norm_num)
  have hd := matrixDZ_schurField_nonsingular a b p
    (C := fun y => (modifiedB a b u y).map star)
    (H := fun y => (modifiedA a b u y).map star) hAd hBd
    (fun i j => (hBd i j).star) (fun i j => (hAd i j).star) hdet
  have he : modifiedSchur a b u = schurField (modifiedA a b u) (modifiedB a b u)
      (fun y => (modifiedB a b u y).map star) (fun y => (modifiedA a b u y).map star) := rfl
  rw [he]
  simpa only [modifiedCompensatedHessian,
    returnField, inverseDerivativeField, Matrix.mul_assoc] using hd

end PowerConvexity
