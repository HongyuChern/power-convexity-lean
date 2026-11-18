import PowerConvexity.Calculus.ModifiedSpectrum
import PowerConvexity.Calculus.LocalDimensionTwo

/-! # Equivariant relabeling of actual Wirtinger frames -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem complexHessian_frame_reindex (a b : ι → E) (e : κ → ι) (u : E → ℝ) (x : E) :
    complexHessian (a ∘ e) (b ∘ e) u x = (complexHessian a b u x).submatrix e e := rfl

theorem modifiedA_frame_reindex (a b : ι → E) (e : κ → ι) (u : E → ℝ) (x : E) :
    modifiedA (a ∘ e) (b ∘ e) u x = (modifiedA a b u x).submatrix e e := rfl

theorem modifiedB_frame_reindex (a b : ι → E) (e : κ → ι) (u : E → ℝ) (x : E) :
    modifiedB (a ∘ e) (b ∘ e) u x = (modifiedB a b u x).submatrix e e := rfl

variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem modifiedSchur_frame_reindex (a b : ι → E) (e : κ ≃ ι) (u : E → ℝ) (x : E) :
    modifiedSchur (a ∘ e) (b ∘ e) u x = (modifiedSchur a b u x).submatrix e e := by
  unfold modifiedSchur matrixSchur
  rw [modifiedA_frame_reindex,modifiedB_frame_reindex,
    ← Matrix.submatrix_map,Matrix.inv_submatrix_equiv,← Matrix.submatrix_map,
    Matrix.submatrix_mul_equiv,Matrix.submatrix_mul_equiv]
  rfl

theorem skewThirdHessian_frame_reindex (a b : ι → E) (e : κ ≃ ι)
    (u : E → ℝ) (k : κ) (x : E) :
    skewThirdHessian (a ∘ e) (b ∘ e) u k x =
      (skewThirdHessian a b u (e k) x).submatrix e e := rfl

end PowerConvexity
