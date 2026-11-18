import PowerConvexity.Analysis.ActualFlatFullJetControlFour

/-! # Continuity from the proved local quantitative jet comparisons -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_local_holder_continuousOn_four {Z : Type*} [NormedAddCommGroup Z]
    {V : Set E} {g : E → Z} {R C beta : ℝ} (hR : 0 < R) (hbeta : 0 < beta)
    (hholder : ∀ x ∈ V, ∀ y ∈ V, ‖x-y‖ < R → ‖g x-g y‖ ≤ C*‖x-y‖^beta) :
    ContinuousOn g V := by
  intro x hx
  have hcont : Continuous (fun y : E => C*‖y-x‖^beta) :=
    continuous_const.mul ((Real.continuous_rpow_const hbeta.le).comp ((continuous_id.sub continuous_const).norm))
  have ht : Tendsto (fun y : E => C*‖y-x‖^beta) (𝓝[V] x) (𝓝 (0 : ℝ)) := by
    simpa only [sub_self,norm_zero,Real.zero_rpow hbeta.ne',mul_zero] using
      (hcont.tendsto x).mono_left nhdsWithin_le_nhds
  have hb : ∀ᶠ y : E in 𝓝[V] x, ‖g y-g x‖ ≤ C*‖y-x‖^beta := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (ball_mem_nhds x hR)] with y hy hnear
    have hn : ‖y-x‖ < R := hnear
    exact hholder y hy x hx hn
  have hz : Tendsto (fun y => g y-g x) (𝓝[V] x) (𝓝 (0 : Z)) := squeeze_zero_norm' hb ht
  have hs := hz.add (tendsto_const_nhds (x := g x))
  change Tendsto g (𝓝[V] x) (𝓝 (g x))
  simpa only [sub_add_cancel,zero_add] using hs

end PowerConvexity
