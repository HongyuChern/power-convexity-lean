import PowerConvexity.Calculus.EuclideanBilinearEntryBound
import CHS.Analysis.HessianHolder

/-! # Actual Frechet Hessian norms from the same real block matrices. -/
set_option autoImplicit false
noncomputable section
open Matrix
open scoped Matrix.Norms.Elementwise
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
local notation "E" => DeGiorgi.AmbientSpace (2+2)

theorem realHessian_norm_sub_le_sixteen_block_norm_two (u : E → ℝ) (x y : E) :
    ‖realHessian u x-realHessian u y‖ ≤
      16*‖realBlockHessian realDirections imagDirections u x-
        realBlockHessian realDirections imagDirections u y‖ := by
  have hh := euclidean_bilinear_norm_le_of_entry_bound
    (realHessian u x-realHessian u y)
    (norm_nonneg (realBlockHessian realDirections imagDirections u x-
      realBlockHessian realDirections imagDirections u y))
    (fun i j => by
      simpa only [ContinuousLinearMap.sub_apply,euclideanHessian] using
        abs_euclideanHessian_sub_le_block_norm u x y i j)
  norm_num only [Fintype.card_fin,Nat.cast_add,Nat.cast_ofNat] at hh
  convert hh using 1 <;> norm_num

theorem realHessian_norm_le_sixteen_entry_bound_two
    {u : E → ℝ} {x : E} {M : ℝ} (hM : 0 ≤ M)
    (hentry : ∀ i j, |euclideanHessian u x i j| ≤ M) :
    ‖realHessian u x‖ ≤ 16*M := by
  have hh := euclidean_bilinear_norm_le_of_entry_bound (realHessian u x) hM hentry
  norm_num only [Fintype.card_fin,Nat.cast_add,Nat.cast_ofNat] at hh
  convert hh using 1 <;> norm_num

end PowerConvexity
