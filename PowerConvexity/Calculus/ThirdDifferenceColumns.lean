import PowerConvexity.Calculus.ThirdDifferenceRows
import PowerConvexity.Calculus.ModifiedDerivatives

/-! # The conjugate column of the actual ReadingTable third derivatives -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem readingTable_third_column_difference {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 3 u x) (a b : ι → E) (k t p : ι) :
    matrixDZ (a p) (b p) (fun y => (pureHessian a b u y).map star) x t k-
      matrixDZ (a p) (b p) (fun y => (complexHessian a b u y).map star) x t k =
      star (skewThirdHessian a b u k x t p) := by
  have hn : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 u y := (hu.of_le (m := 2) (by norm_num)).eventually (by simp)
  have hB : (fun y => star (pureHessian a b u y t k)) =ᶠ[𝓝 x]
      (fun y => star (pureHessian a b u y k t)) := by
    filter_upwards [hn] with y hy
    exact congrArg star (pureHessian_entry_symm hy a b t k)
  have hA : (fun y => star (complexHessian a b u y t k)) =ᶠ[𝓝 x]
      (fun y => complexHessian a b u y k t) := by
    filter_upwards [hn] with y hy
    exact (complexHessian_isHermitian hy a b).apply k t
  have hw := congrArg (fun M : Matrix ι ι ℂ => M p t) (skewThirdHessian_conjTranspose hu a b k)
  change star (skewThirdHessian a b u k x t p) = -skewThirdHessian a b u k x p t at hw
  rw [hw,skewThirdHessian_entry_difference hu a b k p t]
  change dz (a p) (b p) (fun y => star (pureHessian a b u y t k)) x-
    dz (a p) (b p) (fun y => star (complexHessian a b u y t k)) x = _
  rw [dz_congr_nhds hB,dz_congr_nhds hA]
  ring

end PowerConvexity
