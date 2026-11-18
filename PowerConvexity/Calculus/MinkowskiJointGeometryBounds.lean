import PowerConvexity.Calculus.MinkowskiJointDefining
import PowerConvexity.Calculus.ParameterLocalThirdDerivativeBounds

/-! # Actual nearby Minkowski charts with common spatial derivative bounds -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter Metric
open scoped ContDiff Topology Pointwise
namespace PowerConvexity
noncomputable section
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
local instance mjgRealSpace : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance mjgRealModule : Module ℝ E := (inferInstance : InnerProductSpace ℝ E).toModule
local instance mjgDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance mjgDualModule : Module ℝ (E →L[ℝ] ℝ) :=
  (inferInstance : NormedSpace ℝ (E →L[ℝ] ℝ)).toModule
local instance mjgDualTopology : TopologicalSpace (E →L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance mjgHessSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance mjgHessModule : Module ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  (inferInstance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ)).toModule
local instance mjgHessTopology : TopologicalSpace (E →L[ℝ] E →L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace

theorem minkowskiDomain_exists_joint_uniform_C3_defining_bounds
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hboundary : HasSmoothLocalDefiningFunction U)
    {s R : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hR : 0 < R)
    {y : E} (hy : y ∈ frontier (minkowskiDomain s U (ball (0 : E) R))) :
    ∃ phi : ℝ × E → ℝ,
      ContDiffAt ℝ ∞ phi (s,y) ∧ phi (s,y) = 0 ∧
      ∃ eta > 0, ∃ A > 0, ∃ L > 0, ∃ r > 0,
        ∀ q ∈ closedBall (s,y) r,
          ContDiffAt ℝ 3 (fun z => phi (q.1,z)) q.2 ∧
          eta ≤ ‖fderiv ℝ (fun z => phi (q.1,z)) q.2‖ ∧
          ‖realHessian (fun z => phi (q.1,z)) q.2‖ ≤ A ∧
          ‖fderiv ℝ (realHessian (fun z => phi (q.1,z))) q.2‖ ≤ L ∧
          (q.1 ∈ Icc (0 : ℝ) 1 →
            ∀ᶠ z in 𝓝 q.2,
              z ∈ minkowskiDomain q.1 U (ball (0 : E) R) ↔ phi (q.1,z) < 0) := by
  obtain ⟨phi,hphi,hphi0,hD,hnear⟩ :=
    minkowskiDomain_exists_joint_smooth_defining_function hU hconv hK hboundary hs hs1 hR hy
  obtain ⟨eta,heta,A,hA,L,hL,r,hr,hbounds⟩ :=
    exists_parameter_local_uniform_third_derivative_bounds ((contDiffAt_infty.mp hphi) 3) hD
  obtain ⟨d,hd,hball⟩ := Metric.mem_nhds_iff.mp hnear.eventually_nhds
  refine ⟨phi,hphi,hphi0,eta,heta,A,hA,L,hL,min r (d/2),
    lt_min hr (half_pos hd),?_⟩
  intro q hq
  have hqbound := hbounds q ((closedBall_subset_closedBall (min_le_left _ _)) hq)
  have hqd : q ∈ ball (s,y) d :=
    closedBall_subset_ball ((min_le_right r (d/2)).trans_lt (half_lt_self hd)) hq
  have hactual := hball hqd
  refine ⟨hqbound.1,hqbound.2.1,hqbound.2.2.1,hqbound.2.2.2,?_⟩
  intro hI
  have hin : Tendsto (fun z : E => (q.1,z)) (𝓝 q.2) (𝓝 q) :=
    (continuousAt_const.prodMk continuousAt_id).tendsto
  filter_upwards [hin.eventually hactual] with z hz
  exact hz.2 hI

end
end PowerConvexity
