import PowerConvexity.Calculus.UniformAffineHessianBound

/-! # Common derivative bounds near a regular C3 level set

The differential lower bound and the second/third derivative upper bounds are
derived from actual local C3 regularity. They hold on a genuine closed ball.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Filter Metric
open scoped ContDiff Topology
namespace PowerConvexity
noncomputable section
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
local instance ltdInstance1 : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance ltdInstance2 : Module ℝ (E →L[ℝ] ℝ) :=
  (inferInstance : NormedSpace ℝ (E →L[ℝ] ℝ)).toModule
local instance ltdInstance3 : TopologicalSpace (E →L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance ltdInstance4 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance ltdInstance5 : Module ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  (inferInstance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ)).toModule
local instance ltdInstance6 : TopologicalSpace (E →L[ℝ] E →L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace

theorem exists_local_uniform_third_derivative_bounds
    {f : E → ℝ} {p : E} (hf : ContDiffAt ℝ 3 f p) (hDf : fderiv ℝ f p ≠ 0) :
    ∃ eta > 0, ∃ A > 0, ∃ L > 0, ∃ R > 0,
      ∀ y ∈ closedBall p R, ContDiffAt ℝ 3 f y ∧ eta ≤ ‖fderiv ℝ f y‖ ∧
        ‖realHessian f y‖ ≤ A ∧ ‖fderiv ℝ (realHessian f) y‖ ≤ L := by
  have hDc : ContinuousAt (fderiv ℝ f) p :=
    (hf.fderiv_right (m := 2) (by norm_num)).continuousAt
  have hHc : ContinuousAt (realHessian f) p :=
    ((hf.fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)).continuousAt
  have hTc :=
    (((hf.fderiv_right (m := 2) (by norm_num)).fderiv_right
      (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)).continuousAt
  let eta : ℝ := ‖fderiv ℝ f p‖/2
  let A : ℝ := ‖realHessian f p‖+1
  let L : ℝ := ‖fderiv ℝ (realHessian f) p‖+1
  have hn : 0 < ‖fderiv ℝ f p‖ := (norm_pos_iff (a := fderiv ℝ f p)).mpr hDf
  have heta : 0 < eta := by dsimp [eta]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hL : 0 < L := by dsimp [L]; positivity
  have hnearD : ∀ᶠ y in 𝓝 p, eta < ‖fderiv ℝ f y‖ :=
    (ContinuousAt.norm (f := fderiv ℝ f) hDc).tendsto.eventually
      (lt_mem_nhds (by dsimp [eta]; linarith))
  have hnearH : ∀ᶠ y in 𝓝 p, ‖realHessian f y‖ < A :=
    (ContinuousAt.norm (f := realHessian f) hHc).tendsto.eventually
      (gt_mem_nhds (by dsimp [A]; linarith))
  have hnearT : ∀ᶠ y in 𝓝 p, ‖fderiv ℝ (realHessian f) y‖ < L :=
    (ContinuousAt.norm (f := fderiv ℝ (realHessian f)) hTc).tendsto.eventually
      (gt_mem_nhds (by dsimp [L]; linarith))
  have hnear : ∀ᶠ y in 𝓝 p, ContDiffAt ℝ 3 f y ∧ eta ≤ ‖fderiv ℝ f y‖ ∧
      ‖realHessian f y‖ ≤ A ∧ ‖fderiv ℝ (realHessian f) y‖ ≤ L := by
    filter_upwards [hf.eventually (by norm_num),hnearD,hnearH,hnearT] with y hy hdy hhy hty
    exact ⟨hy,hdy.le,hhy.le,hty.le⟩
  obtain ⟨d,hd,hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨eta,heta,A,hA,L,hL,d/2,by positivity,?_⟩
  intro y hy
  exact hball (closedBall_subset_ball (by linarith : d/2 < d) hy)

end
end PowerConvexity
