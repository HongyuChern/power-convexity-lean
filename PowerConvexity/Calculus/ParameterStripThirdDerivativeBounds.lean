import PowerConvexity.Calculus.ParameterLocalThirdDerivativeBounds

/-! # Actual common spatial C3 bounds on a fixed ball for a jointly C4 strip -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter Metric
open scoped ContDiff Topology
namespace PowerConvexity
noncomputable section
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
local instance pstDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance pstDualModule : Module ℝ (E →L[ℝ] ℝ) :=
  (inferInstance : NormedSpace ℝ (E →L[ℝ] ℝ)).toModule
local instance pstDualTopology : TopologicalSpace (E →L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance pstHessSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance pstHessModule : Module ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  (inferInstance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ)).toModule
local instance pstHessTopology : TopologicalSpace (E →L[ℝ] E →L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace

theorem exists_parameter_strip_uniform_third_derivative_bounds
    {F : ℝ × E → ℝ} {s delta : ℝ} (hdelta : 0 < delta)
    (hF : ContDiffOn ℝ 4 F (ball s delta ×ˢ (univ : Set E))) (p : E) (R : ℝ) :
    ∃ A > 0, ∃ L > 0, ∀ t ∈ closedBall s (delta/2), ∀ x ∈ closedBall p R,
      ContDiffAt ℝ 3 (fun y => F (t,y)) x ∧
      ‖realHessian (fun y => F (t,y)) x‖ ≤ A ∧
      ‖fderiv ℝ (realHessian (fun y => F (t,y))) x‖ ≤ L := by
  let K : Set (ℝ × E) := closedBall s (delta/2) ×ˢ closedBall p R
  have hK : IsCompact K := (isCompact_closedBall s (delta/2)).prod (isCompact_closedBall p R)
  have hC3 (q : ℝ × E) (hq : q ∈ K) : ContDiffAt ℝ 3 F q := by
    apply (hF.contDiffAt ((isOpen_ball.prod isOpen_univ).mem_nhds ?_)).of_le (by norm_num)
    exact ⟨closedBall_subset_ball (by linarith : delta/2 < delta) hq.1,mem_univ q.2⟩
  have hD (q : ℝ × E) (hq : q ∈ K) : ContDiffAt ℝ 2
      (fun z : ℝ × E => fderiv ℝ (fun y => F (z.1,y)) z.2) q :=
    parameter_fiber_fderiv_contDiffAt (n := 2) (hC3 q hq)
  have hH (q : ℝ × E) (hq : q ∈ K) : ContDiffAt ℝ 1
      (fun z : ℝ × E => realHessian (fun y => F (z.1,y)) z.2) q :=
    parameter_fiber_fderiv_contDiffAt (n := 1) (hD q hq)
  have hHc : ContinuousOn (fun z : ℝ × E => realHessian (fun y => F (z.1,y)) z.2) K :=
    fun q hq => (hH q hq).continuousAt.continuousWithinAt
  have hTc : ContinuousOn
      (fun z : ℝ × E => fderiv ℝ (realHessian (fun y => F (z.1,y))) z.2) K :=
    fun q hq => (parameter_fiber_fderiv_contDiffAt (n := 0) (hH q hq)).continuousAt.continuousWithinAt
  obtain ⟨A0,hA0⟩ := (hK.image_of_continuousOn hHc).isBounded.exists_norm_le
  obtain ⟨L0,hL0⟩ := (hK.image_of_continuousOn hTc).isBounded.exists_norm_le
  refine ⟨|A0|+1,by positivity,|L0|+1,by positivity,?_⟩
  intro t ht x hx
  have hq : (t,x) ∈ K := ⟨ht,hx⟩
  refine ⟨(hC3 (t,x) hq).comp x (contDiffAt_const.prodMk contDiffAt_id),?_,?_⟩
  · exact (hA0 _ (mem_image_of_mem _ hq)).trans (by linarith [le_abs_self A0])
  · exact (hL0 _ (mem_image_of_mem _ hq)).trans (by linarith [le_abs_self L0])

end
end PowerConvexity
