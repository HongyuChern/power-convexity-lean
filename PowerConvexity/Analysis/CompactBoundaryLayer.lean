import PowerConvexity.Calculus.BoundaryPowerHessian

/-! # A uniform level collar from pointwise boundary neighborhoods -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology ContDiff
namespace PowerConvexity
variable {E : Type*} [TopologicalSpace E]

theorem exists_level_collar_of_boundary_germs
    {U : Set E} (hU : IsOpen U) (hK : IsCompact (closure U)) {u : E → ℝ}
    (huc : ContinuousOn u (closure U)) (hneg : ∀ x ∈ U, u x < 0)
    {P : E → Prop} (hfront : ∀ x ∈ frontier U, ∀ᶠ y in 𝓝 x, y ∈ U → P y) :
    ∃ ε > 0, ∀ y ∈ U, -ε < u y → P y := by
  let V := interior {y | y ∈ U → P y}
  have hV : IsOpen V := isOpen_interior
  have hFV : frontier U ⊆ V := fun x hx => mem_interior_iff_mem_nhds.mpr (hfront x hx)
  let K := closure U \ V
  have hKC : IsCompact K := hK.diff hV
  have hKU : K ⊆ U := by
    intro x hx
    by_contra hn
    have hxf : x ∈ frontier U := by rw [hU.frontier_eq]; exact ⟨hx.1,hn⟩
    exact hx.2 (hFV hxf)
  by_cases hne : K.Nonempty
  · obtain ⟨x,hx,hmax⟩ := hKC.exists_isMaxOn hne (huc.mono (diff_subset))
    have hnx := hneg x (hKU hx)
    refine ⟨-u x/2,by linarith,?_⟩
    intro y hy huy
    have hyV : y ∈ V := by
      by_contra hn
      have hh : u y ≤ u x := hmax (show y ∈ K from ⟨subset_closure hy,hn⟩)
      linarith
    exact (interior_subset hyV) hy
  · refine ⟨1,by norm_num,?_⟩
    intro y hy _
    have hyV : y ∈ V := by
      by_contra hn
      exact hne ⟨y,subset_closure hy,hn⟩
    exact (interior_subset hyV) hy

end PowerConvexity
