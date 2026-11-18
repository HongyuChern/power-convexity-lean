import PowerConvexity.Calculus.ConvexLocalDefiningCriterion

/-! # A uniform local defining criterion for convex fibers

A common product neighborhood and a fixed negative witness, preserved for
nearby parameters by continuity, make the intermediate-value argument
uniform. The parameter restriction may be a closed interval, so this
criterion also applies at a one-sided endpoint.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter Metric
open scoped ContDiff Topology
namespace PowerConvexity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {P : Type*} [TopologicalSpace P]

theorem parameter_convex_local_defining_of_negative_side_and_zero_exclusion
    {V : P → Set E} (hV : ∀ t, Convex ℝ (V t))
    {S : Set P} {F : P × E → ℝ} {s : P} {x : E}
    (hfx : F (s,x) = 0) (hDf : fderiv ℝ (fun y => F (s,y)) x ≠ 0)
    (hcont : ∀ᶠ p in 𝓝 (s,x), ContinuousAt F p)
    (hneg : ∀ᶠ p in 𝓝 (s,x), p.1 ∈ S → F p < 0 → p.2 ∈ V p.1)
    (hzero : ∀ᶠ p in 𝓝 (s,x), p.1 ∈ S → F p = 0 → p.2 ∉ V p.1) :
    ∀ᶠ p in 𝓝 (s,x), p.1 ∈ S → (p.2 ∈ V p.1 ↔ F p < 0) := by
  have hnear : ∀ᶠ p in 𝓝 (s,x),
      (p.1 ∈ S → F p < 0 → p.2 ∈ V p.1) ∧
      (p.1 ∈ S → F p = 0 → p.2 ∉ V p.1) ∧ ContinuousAt F p := by
    filter_upwards [hneg,hzero,hcont] with p hn hz hc
    exact ⟨hn,hz,hc⟩
  obtain ⟨A,hA,B,hB,hAB⟩ := mem_nhds_prod_iff.mp hnear
  obtain ⟨δ,hδ,hδB⟩ := Metric.mem_nhds_iff.mp hB
  have hall (t : P) (ht : t ∈ A) (y : E) (hy : y ∈ ball x δ) :
      (t ∈ S → F (t,y) < 0 → y ∈ V t) ∧
      (t ∈ S → F (t,y) = 0 → y ∉ V t) ∧ ContinuousAt F (t,y) :=
    hAB (show (t,y) ∈ A ×ˢ B from ⟨ht,hδB hy⟩)
  have hex : ∃ b ∈ ball x δ, F (s,b) < 0 := by
    by_contra! h
    apply hDf
    apply IsLocalMin.fderiv_eq_zero
    change ∀ᶠ z in 𝓝 x, F (s,x) ≤ F (s,z)
    filter_upwards [ball_mem_nhds x hδ] with z hz
    rw [hfx]
    exact h z hz
  obtain ⟨b,hb,hfb⟩ := hex
  have hcb : ContinuousAt F (s,b) := (hall s (mem_of_mem_nhds hA) b hb).2.2
  have hbnear : ∀ᶠ t in 𝓝 s, F (t,b) < 0 :=
    (hcb.comp (f := fun t : P => (t,b))
      (continuousAt_id.prodMk continuousAt_const)).tendsto.eventually
      (gt_mem_nhds hfb)
  have hAnear : ∀ᶠ p : P × E in 𝓝 (s,x), p.1 ∈ A :=
    continuousAt_fst.tendsto.eventually hA
  have hbnear' : ∀ᶠ p : P × E in 𝓝 (s,x), F (p.1,b) < 0 :=
    (show Tendsto (fun p : P × E => p.1) (𝓝 (s,x)) (𝓝 s) from
      continuousAt_fst.tendsto).eventually hbnear
  have hynear : ∀ᶠ p : P × E in 𝓝 (s,x), p.2 ∈ ball x δ :=
    continuousAt_snd.tendsto.eventually (ball_mem_nhds x hδ)
  filter_upwards [hAnear,hbnear',hynear] with p hpA hpb hpy
  intro hpS
  have hbV : b ∈ V p.1 := (hall p.1 hpA b hb).1 hpS hpb
  have hc : ContinuousOn (fun y => F (p.1,y)) (ball x δ ∩ V p.1) := by
    intro z hz
    exact ((hall p.1 hpA z hz.1).2.2.comp
      (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  constructor
  · intro hpV
    by_contra hnot
    obtain ⟨z,hz,hfz⟩ := ((convex_ball x δ).inter (hV p.1)).isPreconnected.intermediate_value₂
      (show b ∈ ball x δ ∩ V p.1 from ⟨hb,hbV⟩)
      (show p.2 ∈ ball x δ ∩ V p.1 from ⟨hpy,hpV⟩)
      hc continuousOn_const hpb.le (not_lt.mp hnot)
    exact (hall p.1 hpA z hz.1).2.1 hpS hfz hz.2
  · exact (hall p.1 hpA p.2 hpy).1 hpS

end PowerConvexity
