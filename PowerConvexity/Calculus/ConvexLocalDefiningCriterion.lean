import PowerConvexity.Calculus.RegularDefiningBoundaryChart
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Order.IntermediateValue

/-! # Recovering the interior side of a regular level in a convex domain

A regular function whose negative side is inside a convex domain and whose
zero level is outside that domain is an actual local defining function.
The missing implication follows from the intermediate value theorem on
the intersection of the domain with a small convex ball.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Filter Metric
open scoped ContDiff Topology
namespace PowerConvexity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem convex_local_defining_of_negative_side_and_zero_exclusion
    {V : Set E} (hV : Convex ℝ V) {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 1 f x) (hfx : f x = 0) (hDf : fderiv ℝ f x ≠ 0)
    (hneg : ∀ᶠ y in 𝓝 x, f y < 0 → y ∈ V)
    (hzero : ∀ᶠ y in 𝓝 x, f y = 0 → y ∉ V) :
    ∀ᶠ y in 𝓝 x, y ∈ V ↔ f y < 0 := by
  have hnear : ∀ᶠ y in 𝓝 x,
      (f y < 0 → y ∈ V) ∧ (f y = 0 → y ∉ V) ∧ ContinuousAt f y := by
    filter_upwards [hneg,hzero,hf.eventually (by norm_num)] with y hn hz hc
    exact ⟨hn,hz,hc.continuousAt⟩
  obtain ⟨δ,hδ,hall⟩ := Metric.mem_nhds_iff.mp hnear
  have hex : ∃ b ∈ ball x δ, f b < 0 := by
    by_contra! h
    apply hDf
    apply IsLocalMin.fderiv_eq_zero
    change ∀ᶠ z in 𝓝 x, f x ≤ f z
    filter_upwards [ball_mem_nhds x hδ] with z hz
    rw [hfx]
    exact h z hz
  obtain ⟨b,hb,hfb⟩ := hex
  have hbV := (hall hb).1 hfb
  have hc : ContinuousOn f (ball x δ ∩ V) := by
    intro z hz
    exact (hall hz.1).2.2.continuousWithinAt
  filter_upwards [ball_mem_nhds x hδ] with y hy
  constructor
  · intro hyV
    by_contra hfnot
    obtain ⟨z,hz,hfz⟩ := ((convex_ball x δ).inter hV).isPreconnected.intermediate_value₂
      (show b ∈ ball x δ ∩ V from ⟨hb,hbV⟩)
      (show y ∈ ball x δ ∩ V from ⟨hy,hyV⟩)
      hc continuousOn_const hfb.le (not_lt.mp hfnot)
    exact (hall hz.1).2.1 hfz hz.2
  · exact (hall hy).1

end PowerConvexity
