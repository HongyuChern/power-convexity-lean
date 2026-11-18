import PowerConvexity.Calculus.FiniteParameterFiberDerivative
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! # Actual common spatial C3 bounds from a joint local C3 function

All radii and derivative bounds precede the fiber parameter. The bounds are
obtained on one compact product ball, using the actual fiber derivatives.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace PowerConvexity
variable {P E : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [ProperSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
local instance ajcbDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance ajcbDualModule : Module ℝ (E →L[ℝ] ℝ) :=
  (inferInstance : NormedSpace ℝ (E →L[ℝ] ℝ)).toModule
local instance ajcbDualTopology : TopologicalSpace (E →L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance ajcbHessSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance ajcbHessModule : Module ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  (inferInstance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ)).toModule
local instance ajcbHessTopology : TopologicalSpace (E →L[ℝ] E →L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace

theorem actual_joint_C3_uniform_fiber_bounds
    {s : P} {F : P × E → ℝ} (hF : ContDiffAt ℝ 3 F (s,0)) :
    ∃ d > 0, ∃ A > 0, ∃ B > 0, ∃ C > 0,
      ∀ p ∈ closedBall s d, ∀ x ∈ closedBall (0 : E) d,
        ContDiffAt ℝ 3 (fun y => F (p,y)) x ∧
        ‖fderiv ℝ (fun y => F (p,y)) x‖ ≤ A ∧
        ‖fderiv ℝ (fderiv ℝ (fun y => F (p,y))) x‖ ≤ B ∧
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y => F (p,y)))) x‖ ≤ C := by
  obtain ⟨r,hr,hnear⟩ := Metric.mem_nhds_iff.mp (hF.eventually (by norm_num))
  let d := r/2
  have hd : 0 < d := half_pos hr
  let K : Set (P × E) := closedBall s d ×ˢ closedBall (0 : E) d
  have hK : IsCompact K := (isCompact_closedBall s d).prod (isCompact_closedBall (0 : E) d)
  have hC3 (q : P × E) (hq : q ∈ K) : ContDiffAt ℝ 3 F q := by
    apply hnear
    have hp : dist q.1 s ≤ d := hq.1
    have hx : dist q.2 0 ≤ d := hq.2
    have hdr : d < r := by dsimp only [d]; linarith
    change max (dist q.1 s) (dist q.2 0) < r
    exact max_lt (hp.trans_lt hdr) (hx.trans_lt hdr)
  let D : P × E → E →L[ℝ] ℝ := fun q => fderiv ℝ (fun y => F (q.1,y)) q.2
  let H : P × E → E →L[ℝ] E →L[ℝ] ℝ :=
    fun q => fderiv ℝ (fderiv ℝ (fun y => F (q.1,y))) q.2
  let T : P × E → E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
    fun q => fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y => F (q.1,y)))) q.2
  have hD (q : P × E) (hq : q ∈ K) : ContDiffAt ℝ 2 D q :=
    finite_parameter_fiber_fderiv_contDiffAt (n := 2) (hC3 q hq)
  have hH (q : P × E) (hq : q ∈ K) : ContDiffAt ℝ 1 H q :=
    finite_parameter_fiber_fderiv_contDiffAt (n := 1) (hD q hq)
  have hT (q : P × E) (hq : q ∈ K) : ContinuousAt T q :=
    (finite_parameter_fiber_fderiv_contDiffAt (n := 0) (hH q hq)).continuousAt
  obtain ⟨A,hA⟩ := (hK.image_of_continuousOn
    (show ContinuousOn D K from fun q hq => (hD q hq).continuousAt.continuousWithinAt)).isBounded.exists_norm_le
  obtain ⟨B,hB⟩ := (hK.image_of_continuousOn
    (show ContinuousOn H K from fun q hq => (hH q hq).continuousAt.continuousWithinAt)).isBounded.exists_norm_le
  obtain ⟨C,hC⟩ := (hK.image_of_continuousOn
    (show ContinuousOn T K from fun q hq => (hT q hq).continuousWithinAt)).isBounded.exists_norm_le
  refine ⟨d,hd,|A|+1,by positivity,|B|+1,by positivity,|C|+1,by positivity,?_⟩
  intro p hp x hx
  have hq : (p,x) ∈ K := ⟨hp,hx⟩
  refine ⟨(hC3 (p,x) hq).comp x (contDiffAt_const.prodMk contDiffAt_id),?_,?_,?_⟩
  · exact (hA _ (mem_image_of_mem _ hq)).trans (by linarith [le_abs_self A])
  · exact (hB _ (mem_image_of_mem _ hq)).trans (by linarith [le_abs_self B])
  · exact (hC _ (mem_image_of_mem _ hq)).trans (by linarith [le_abs_self C])

end PowerConvexity
