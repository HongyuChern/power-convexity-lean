import PowerConvexity.Calculus.FrameReindex
import PowerConvexity.Calculus.MatrixIdentities

/-! # Reindexing the actual second elliptic contraction -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace PowerConvexity
open CHS.Calculus
variable {E ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem matrixL_frame_reindex (a b : ι → E) (e : κ ≃ ι) (u : E → ℝ)
    (M : E → Matrix ι ι ℂ) (x : E) :
    matrixL (a ∘ e) (b ∘ e) u (fun y => (M y).submatrix e e) x =
      (matrixL a b u M x).submatrix e e := by
  ext i j
  rw [Matrix.submatrix_apply,matrixL_entry,matrixL_entry,
    complexHessian_frame_reindex,Matrix.inv_submatrix_equiv]
  simp only [Matrix.submatrix_apply,Function.comp_apply]
  let F : ι → ι → ℂ := fun p q => (complexHessian a b u x)⁻¹ q p *
    dz (a q) (-b q) (dz (a p) (b p) (fun y => M y (e i) (e j))) x
  change (∑ p : κ, ∑ q : κ, F (e p) (e q)) = ∑ p : ι, ∑ q : ι, F p q
  calc
    _ = ∑ p : ι, ∑ q : κ, F p (e q) := e.sum_comp (fun p => ∑ q : κ, F p (e q))
    _ = _ := Finset.sum_congr rfl fun p _ => e.sum_comp (F p)

end PowerConvexity
