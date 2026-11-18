import PowerConvexity.Calculus.EquicontinuousDerivativeFamilies
import PowerConvexity.Calculus.RealHessianRules

/-! # First jets from joint values and bounded Hessians

This proof uses only the mean value theorem and finite differences. In
particular, it does not use convexity of the power transform or a convexity
endpoint that the manuscript's deformation is meant to prove.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Metric Filter
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {T E : Type*} [TopologicalSpace T] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [ProperSpace E]

theorem fderiv_family_continuousAt_of_joint_values_boundedHessian
    {u : T → E → ℝ} {t0 : T} {x0 : E} {R K : ℝ}
    (hR : 0 < R) (hK : 0 ≤ K)
    (hval : ∀ y ∈ closedBall x0 R,
      ContinuousAt (fun p : T × E => u p.1 p.2) (t0,y))
    (hdata : ∀ᶠ t in 𝓝 t0, ∀ y ∈ closedBall x0 R,
      ContDiffAt ℝ 2 (u t) y ∧ ‖realHessian (u t) y‖ ≤ K) :
    ContinuousAt (fun p : T × E => fderiv ℝ (u p.1) p.2) (t0,x0) := by
  have hdiff : ∀ᶠ t in 𝓝 t0, ∀ y ∈ closedBall x0 R, DifferentiableAt ℝ (u t) y := by
    filter_upwards [hdata] with t ht
    exact fun y hy => (ht y hy).1.differentiableAt (by norm_num)
  apply family_fderiv_continuousAt_of_uniform_oscillation hR hval hdiff
  intro η hη
  let r := min R (η/(K+1))
  have hK1 : 0 < K+1 := by linarith
  have hr : 0 < r := lt_min hR (div_pos hη hK1)
  have hrR : r ≤ R := min_le_left _ _
  have hrη : r*(K+1) ≤ η := (le_div_iff₀ hK1).mp (min_le_right _ _)
  refine ⟨r,hr,hrR,?_⟩
  filter_upwards [hdata] with t ht
  intro y hy
  have hsub := closedBall_subset_closedBall hrR hy
  have hD (z : E) (hz : z ∈ closedBall x0 R) :
      DifferentiableAt ℝ (fderiv ℝ (u t)) z :=
    ((ht z hz).1.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hh := (convex_closedBall x0 R).norm_image_sub_le_of_norm_fderiv_le
    hD (fun z hz => (ht z hz).2) (mem_closedBall_self hR.le) hsub
  have hyr : ‖y-x0‖ ≤ r := by simpa only [mem_closedBall,dist_eq_norm] using hy
  have hm : K*‖y-x0‖ ≤ K*r := mul_le_mul_of_nonneg_left hyr hK
  exact hh.trans (by nlinarith)

end PowerConvexity
