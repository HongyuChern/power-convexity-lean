import PowerConvexity.Algebra.TakagiTwo
import PowerConvexity.Calculus.ModifiedSpectrum
import PowerConvexity.Algebra.EigenvaluesTwo

/-! # Simultaneous normalization of the actual modified Hessians in dimension two -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff ComplexOrder
namespace PowerConvexity

theorem exists_simultaneous_takagi_two {A B : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : A.PosDef) (hB : B.transpose = B) :
    ∃ (Q : Matrix (Fin 2) (Fin 2) ℂ) (d : Fin 2 → ℝ),
      IsUnit Q.det ∧ Q*A*Q.conjTranspose = 1 ∧
      0 ≤ d 1 ∧ d 1 ≤ d 0 ∧
      Q*B*Q.transpose = Matrix.diagonal (fun i => (d i:ℂ)) := by
  obtain ⟨P,hP,hPA⟩ := exists_complex_normalization hA
  have hBP : (P*B*P.transpose).transpose = P*B*P.transpose :=
    symmetric_congruence_transpose hB P
  obtain ⟨U,d,hU,hUU,hd1,horder,hdiag⟩ := exists_takagi_two hBP
  refine ⟨U*P,d, ?_, ?_,hd1,horder, ?_⟩
  · rw [Matrix.det_mul]; exact hU.mul hP
  · rw [Matrix.conjTranspose_mul]
    calc
      U*P*A*(P.conjTranspose*U.conjTranspose) =
        U*(P*A*P.conjTranspose)*U.conjTranspose := by noncomm_ring
      _ = 1 := by rw [hPA,Matrix.mul_one,hUU]
  · rw [Matrix.transpose_mul]
    calc
      U*P*B*(P.transpose*U.transpose) = U*(P*B*P.transpose)*U.transpose := by noncomm_ring
      _ = _ := hdiag

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
open CHS.Calculus

/-- The frame exists whenever the actual modified mixed Hessian is positive definite.
This does not preserve density one; the transformed density is given by the
already proved determinant covariance. -/
theorem exists_modified_takagi_frame_two_of_modifiedA {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hx : u x < 0) (a b : Fin 2 → E)
    (hA : (modifiedA a b u x).PosDef) :
    ∃ (Q : Matrix (Fin 2) (Fin 2) ℂ) (d : Fin 2 → ℝ),
      IsUnit Q.det ∧ 0 ≤ d 1 ∧ d 1 ≤ d 0 ∧
      modifiedA (complexFrameReal Q a b) (complexFrameImag Q a b) u x = 1 ∧
      modifiedB (complexFrameReal Q a b) (complexFrameImag Q a b) u x =
        Matrix.diagonal (fun i => (d i:ℂ)) ∧
      modifiedK (complexFrameReal Q a b) (complexFrameImag Q a b) u x =
        Matrix.diagonal (fun i => ((1-d i^2:ℝ):ℂ)) := by
  obtain ⟨Q,d,hQ,hQA,hd1,horder,hQB⟩ := exists_simultaneous_takagi_two
    hA (modifiedB_transpose hu a b)
  have hAm : modifiedA (complexFrameReal Q a b) (complexFrameImag Q a b) u x = 1 := by
    rw [modifiedA_complexFrame hu hx, hQA]
  have hBm : modifiedB (complexFrameReal Q a b) (complexFrameImag Q a b) u x =
      Matrix.diagonal (fun i => (d i:ℂ)) := by
    rw [modifiedB_complexFrame hu hx, hQB]
  refine ⟨Q,d,hQ,hd1,horder,hAm,hBm, ?_⟩
  unfold modifiedK modifiedSchur
  rw [hAm,hBm,inv_one,Matrix.mul_one,matrixSchur_one_real_diagonal]

/-- On the classical strict psh branch the required positivity of modifiedA
follows from the actual complex Hessian and the negative potential value. -/
theorem exists_modified_takagi_frame_two {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hx : u x < 0) (a b : Fin 2 → E)
    (hA : (complexHessian a b u x).PosDef) :
    ∃ (Q : Matrix (Fin 2) (Fin 2) ℂ) (d : Fin 2 → ℝ),
      IsUnit Q.det ∧ 0 ≤ d 1 ∧ d 1 ≤ d 0 ∧
      modifiedA (complexFrameReal Q a b) (complexFrameImag Q a b) u x = 1 ∧
      modifiedB (complexFrameReal Q a b) (complexFrameImag Q a b) u x =
        Matrix.diagonal (fun i => (d i:ℂ)) ∧
      modifiedK (complexFrameReal Q a b) (complexFrameImag Q a b) u x =
        Matrix.diagonal (fun i => ((1-d i^2:ℝ):ℂ)) :=
  exists_modified_takagi_frame_two_of_modifiedA hu hx a b (modifiedA_posDef a b hx hA)

end PowerConvexity
