import PowerConvexity.Calculus.ComplexFrameCMAJets
import PowerConvexity.Calculus.RealHessianBlockNormTwo

/-! # Physical Hessian differences from actual real-block differences

A fixed real isometry transfers the actual full Frechet Hessian. The factor
16 is the square of the real dimension four; the same potentials and points
occur on both sides, and no independently selected jets are introduced.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open scoped ContDiff Matrix.Norms.Elementwise
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem actual_isometric_hessian_difference_from_block_two
    (T : AmbientSpace (2+2) ≃ₗᵢ[ℝ] E) {v : E → ℝ}
    {x y : AmbientSpace (2+2)}
    (hx : ContDiffAt ℝ 2 v (T x)) (hy : ContDiffAt ℝ 2 v (T y)) :
    ‖realHessian v (T x)-realHessian v (T y)‖ ≤
      16*‖realBlockHessian realDirections imagDirections (fun z => v (T z)) x-
        realBlockHessian realDirections imagDirections (fun z => v (T z)) y‖ := by
  have hh := bilinear_norm_le_of_isometric_entries T
    (realHessian v (T x)-realHessian v (T y))
    (norm_nonneg (realBlockHessian realDirections imagDirections (fun z => v (T z)) x-
      realBlockHessian realDirections imagDirections (fun z => v (T z)) y))
    (fun i j => by
      have hb := abs_euclideanHessian_sub_le_block_norm (fun z => v (T z)) x y i j
      simpa only [ContinuousLinearMap.sub_apply,euclideanHessian,
        realHessian_comp_linearIsometry T hx,realHessian_comp_linearIsometry T hy] using hb)
  norm_num only [Nat.cast_add,Nat.cast_ofNat] at hh
  exact hh

end PowerConvexity
