import PowerConvexity.Calculus.ParameterFiberDerivative
import PowerConvexity.Calculus.LocalThirdDerivativeBounds

/-! # Common actual spatial C3 bounds on a parameter-space closed ball -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open Set Filter Metric
open scoped ContDiff Topology
namespace PowerConvexity
noncomputable section
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
local instance ptdDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance ptdDualModule : Module ℝ (E →L[ℝ] ℝ) :=
  (inferInstance : NormedSpace ℝ (E →L[ℝ] ℝ)).toModule
local instance ptdDualTopology : TopologicalSpace (E →L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance ptdHessSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance ptdHessModule : Module ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  (inferInstance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ)).toModule
local instance ptdHessTopology : TopologicalSpace (E →L[ℝ] E →L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace

theorem exists_parameter_local_uniform_third_derivative_bounds
    {F : ℝ × E → ℝ} {p : ℝ × E} (hF : ContDiffAt ℝ 3 F p)
    (hDf : fderiv ℝ (fun y => F (p.1,y)) p.2 ≠ 0) :
    ∃ eta > 0, ∃ A > 0, ∃ L > 0, ∃ r > 0,
      ∀ q ∈ closedBall p r,
        ContDiffAt ℝ 3 (fun y => F (q.1,y)) q.2 ∧
        eta ≤ ‖fderiv ℝ (fun y => F (q.1,y)) q.2‖ ∧
        ‖realHessian (fun y => F (q.1,y)) q.2‖ ≤ A ∧
        ‖fderiv ℝ (realHessian (fun y => F (q.1,y))) q.2‖ ≤ L := by
  have hD : ContDiffAt ℝ 2
      (fun q : ℝ × E => fderiv ℝ (fun y => F (q.1,y)) q.2) p :=
    parameter_fiber_fderiv_contDiffAt (n := 2) hF
  have hH : ContDiffAt ℝ 1
      (fun q : ℝ × E => realHessian (fun y => F (q.1,y)) q.2) p :=
    parameter_fiber_fderiv_contDiffAt (n := 1) hD
  have hT := (parameter_fiber_fderiv_contDiffAt (n := 0) hH).continuousAt
  let eta : ℝ := ‖fderiv ℝ (fun y => F (p.1,y)) p.2‖/2
  let A : ℝ := ‖realHessian (fun y => F (p.1,y)) p.2‖+1
  let L : ℝ := ‖fderiv ℝ (realHessian (fun y => F (p.1,y))) p.2‖+1
  have hn : 0 < ‖fderiv ℝ (fun y => F (p.1,y)) p.2‖ := norm_pos_iff.mpr hDf
  have heta : 0 < eta := by dsimp [eta]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hL : 0 < L := by dsimp [L]; positivity
  have hnearD : ∀ᶠ q : ℝ × E in 𝓝 p, eta < ‖fderiv ℝ (fun y => F (q.1,y)) q.2‖ :=
    (ContinuousAt.norm (f := fun q : ℝ × E => fderiv ℝ (fun y => F (q.1,y)) q.2)
      hD.continuousAt).tendsto.eventually
      (lt_mem_nhds (show eta < ‖fderiv ℝ (fun y => F (p.1,y)) p.2‖ by
        dsimp [eta]; linarith))
  have hnearH : ∀ᶠ q : ℝ × E in 𝓝 p, ‖realHessian (fun y => F (q.1,y)) q.2‖ < A :=
    (ContinuousAt.norm (f := fun q : ℝ × E => realHessian (fun y => F (q.1,y)) q.2)
      hH.continuousAt).tendsto.eventually
      (gt_mem_nhds (by dsimp [A]; linarith))
  have hnearT : ∀ᶠ q : ℝ × E in 𝓝 p,
      ‖fderiv ℝ (realHessian (fun y => F (q.1,y))) q.2‖ < L :=
    (ContinuousAt.norm (f := fun q : ℝ × E => fderiv ℝ (realHessian (fun y => F (q.1,y))) q.2)
      hT).tendsto.eventually
      (gt_mem_nhds (by dsimp [L]; linarith))
  have hnear : ∀ᶠ q : ℝ × E in 𝓝 p,
      ContDiffAt ℝ 3 (fun y => F (q.1,y)) q.2 ∧
      eta ≤ ‖fderiv ℝ (fun y => F (q.1,y)) q.2‖ ∧
      ‖realHessian (fun y => F (q.1,y)) q.2‖ ≤ A ∧
      ‖fderiv ℝ (realHessian (fun y => F (q.1,y))) q.2‖ ≤ L := by
    filter_upwards [hF.eventually (by norm_num),hnearD,hnearH,hnearT]
      with q hq hDq hHq hTq
    exact ⟨hq.comp q.2 (contDiffAt_const.prodMk contDiffAt_id),hDq.le,hHq.le,hTq.le⟩
  obtain ⟨d,hd,hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨eta,heta,A,hA,L,hL,d/2,by positivity,?_⟩
  intro q hq
  exact hball (closedBall_subset_ball (by linarith : d/2 < d) hq)

end
end PowerConvexity
