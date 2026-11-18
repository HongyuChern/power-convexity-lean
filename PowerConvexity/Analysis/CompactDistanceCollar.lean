import PowerConvexity.Analysis.CompactBoundaryLayer
import PowerConvexity.Calculus.DistanceInteriorTruncation

/-! # A uniform distance collar from pointwise boundary germs -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped Topology
namespace PowerConvexity
variable {E : Type*} [MetricSpace E]

theorem exists_distance_collar_of_boundary_germs
    {U : Set E} (hK : IsCompact (closure U)) (hF : (frontier U).Nonempty)
    {P : E → Prop} (hgerm : ∀ x ∈ frontier U, ∀ᶠ y in 𝓝 x, y ∈ U → P y) :
    ∃ δ > 0, ∀ y ∈ U, infDist y (frontier U) < δ → P y := by
  let V := interior {y | y ∈ U → P y}
  have hV : IsOpen V := isOpen_interior
  have hFV : frontier U ⊆ V := fun x hx => mem_interior_iff_mem_nhds.mpr (hgerm x hx)
  let K := closure U \ V
  have hKC : IsCompact K := hK.diff hV
  by_cases hne : K.Nonempty
  · obtain ⟨x,hx,hmin⟩ := hKC.exists_isMinOn hne (continuous_infDist_pt (frontier U)).continuousOn
    have hxF : x ∉ frontier U := fun h => hx.2 (hFV h)
    have hd : 0 < infDist x (frontier U) :=
      (isClosed_frontier.notMem_iff_infDist_pos hF).mp hxF
    refine ⟨infDist x (frontier U)/2,by positivity,?_⟩
    intro y hy hdy
    have hyV : y ∈ V := by
      by_contra hn
      have hh : infDist x (frontier U) ≤ infDist y (frontier U) :=
        hmin (show y ∈ K from ⟨subset_closure hy,hn⟩)
      linarith
    exact (interior_subset hyV) hy
  · refine ⟨1,by norm_num,?_⟩
    intro y hy _
    have hyV : y ∈ V := by
      by_contra hn
      exact hne ⟨y,subset_closure hy,hn⟩
    exact (interior_subset hyV) hy

end PowerConvexity
