import PowerConvexity.Calculus.PositiveMatrixGradientSquareTwo
import PowerConvexity.Calculus.DoubleZeroContactTwo

/-! # Actual modified-Schur square-gradient errors near a normalized double zero -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem modifiedSchur_entry_gradient_sq_bound_at_double_zero_two
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 4 u x) (hneg : u x < 0)
    (a b : Fin 2 → E) (hpsh : (complexHessian a b u x).PosDef)
    (hM : ∀ᶠ y in 𝓝 x, (modifiedSchur a b u y).PosSemidef)
    (hI : modifiedA a b u x = 1)
    (hD : modifiedB a b u x = Matrix.diagonal (fun _ => (1:ℂ))) :
    ∃ C > 0, ∀ᶠ y in 𝓝 x, ∀ i j : Fin 2,
      ‖fderiv ℝ (fun z => (modifiedSchur a b u z i j).re) y‖^2+
      ‖fderiv ℝ (fun z => (modifiedSchur a b u z i j).im) y‖^2 ≤
        C*(modifiedSchur a b u y).trace.re := by
  exact exists_matrix_all_entry_gradient_sq_bound_at_zero_two
    (modifiedSchur_contDiffAt_two hu hneg a b hpsh) hM
    (modifiedSchur_double_zero_matrix a b hI hD)

end PowerConvexity
