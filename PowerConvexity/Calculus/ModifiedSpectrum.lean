import PowerConvexity.Algebra.SchurSpectrum
import PowerConvexity.Calculus.CoordinateCovariance
import PowerConvexity.Calculus.ModifiedSchurResidual

/-! # The genuine Schur quotient field and its Hermitian representative -/

set_option autoImplicit false
open scoped ContDiff ComplexOrder

namespace PowerConvexity
open CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def modifiedK (a b : ι → E) (u : E → ℝ) (x : E) : Matrix ι ι ℂ :=
  modifiedSchur a b u x * (modifiedA a b u x)⁻¹

theorem modifiedB_transpose {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (a b : ι → E) :
    (modifiedB a b u x).transpose = modifiedB a b u x := by
  ext i j
  simp only [Matrix.transpose_apply, modifiedB_eq_weight]
  rw [pureHessian_entry_symm hu a b j i]
  ring

theorem modifiedSchur_isHermitian {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hx : u x < 0) (a b : ι → E)
    (hA : (complexHessian a b u x).PosDef) :
    (modifiedSchur a b u x).IsHermitian :=
  matrixSchur_isHermitian (modifiedA_posDef a b hx hA).isHermitian
    (modifiedB_transpose hu a b)

theorem modifiedK_contDiffAt_two {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 4 u x) (hx : u x < 0) (a b : ι → E)
    (hA : (complexHessian a b u x).PosDef) (i j : ι) :
    ContDiffAt ℝ 2 (fun y => modifiedK a b u y i j) x := by
  have hMA := modifiedA_posDef a b hx hA
  apply matrix_product_contDiffAt (modifiedSchur_contDiffAt_two hu hx a b hA)
  exact field_inverse_contDiffAt_of_det_ne_zero (modifiedA_contDiffAt_two hu hx a b)
    (ne_of_gt hMA.det_pos)

theorem exists_modifiedA_normalizing_frame {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hx : u x < 0) (a b : ι → E)
    (hA : (complexHessian a b u x).PosDef) :
    ∃ Q : Matrix ι ι ℂ, IsUnit Q.det ∧
      modifiedA (complexFrameReal Q a b) (complexFrameImag Q a b) u x = 1 := by
  obtain ⟨Q, hQ, hn⟩ := exists_complex_normalization (modifiedA_posDef a b hx hA)
  refine ⟨Q, hQ, ?_⟩
  rw [modifiedA_complexFrame hu hx]
  exact hn

theorem modifiedK_hermitian_representative {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hx : u x < 0) (a b : ι → E)
    (hA : (complexHessian a b u x).PosDef) :
    let Q := whiteningMatrix (modifiedA a b u x)
    let H := schurHermitianRepresentative (modifiedA a b u x) (modifiedB a b u x)
    IsUnit Q.det ∧ H.IsHermitian ∧ H = Q * modifiedK a b u x * Q⁻¹ := by
  have hMA := modifiedA_posDef a b hx hA
  refine ⟨(whiteningMatrix_normalizes hMA).1, ?_, ?_⟩
  · exact schurHermitianRepresentative_isHermitian hMA.isHermitian
      (modifiedB_transpose hu a b)
  · exact schurHermitianRepresentative_similarity hMA

end PowerConvexity
