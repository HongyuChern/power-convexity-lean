import PowerConvexity.Analysis.CompactBoundaryLayer

/-! # Negative level truncations stay strictly inside the classical domain -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped Topology ContDiff
namespace PowerConvexity
variable {E : Type*} [TopologicalSpace E]

def negativeLevelDomain (U : Set E) (u : E → ℝ) (ε : ℝ) : Set E :=
  U ∩ u ⁻¹' Iio (-ε)

theorem negativeLevelDomain_isOpen {U : Set E} (hU : IsOpen U) {u : E → ℝ}
    (hu : ContinuousOn u (closure U)) (ε : ℝ) : IsOpen (negativeLevelDomain U u ε) :=
  (hu.mono subset_closure).isOpen_inter_preimage hU isOpen_Iio

theorem negativeLevelDomain_closure_subset
    {U : Set E} (hU : IsOpen U) {u : E → ℝ} (hu : ContinuousOn u (closure U))
    (hb : ∀ x ∈ frontier U, u x = 0) {ε : ℝ} (hε : 0 < ε) :
    closure (negativeLevelDomain U u ε) ⊆ {x | x ∈ U ∧ u x ≤ -ε} := by
  have hc : IsClosed (closure U ∩ u ⁻¹' Iic (-ε)) :=
    hu.preimage_isClosed_of_isClosed isClosed_closure isClosed_Iic
  have hsub : negativeLevelDomain U u ε ⊆ closure U ∩ u ⁻¹' Iic (-ε) :=
    fun x hx => ⟨subset_closure hx.1,(show u x < -ε from hx.2).le⟩
  have hcl := closure_minimal hsub hc
  intro x hx
  have hh := hcl hx
  refine ⟨?_,hh.2⟩
  by_contra hn
  have hxf : x ∈ frontier U := by rw [hU.frontier_eq]; exact ⟨hh.1,hn⟩
  have hz := hb x hxf
  have hle : u x ≤ -ε := hh.2
  linarith

theorem negativeLevelDomain_isCompact_closure
    {U : Set E} (hK : IsCompact (closure U)) (u : E → ℝ) (ε : ℝ) :
    IsCompact (closure (negativeLevelDomain U u ε)) :=
  hK.of_isClosed_subset isClosed_closure (closure_mono inter_subset_left)

theorem negativeLevelDomain_frontier_value
    {U : Set E} (hU : IsOpen U) {u : E → ℝ} (hu : ContinuousOn u (closure U))
    (hb : ∀ x ∈ frontier U, u x = 0) {ε : ℝ} (hε : 0 < ε) :
    ∀ x ∈ frontier (negativeLevelDomain U u ε), x ∈ U ∧ u x = -ε := by
  intro x hx
  have hh := negativeLevelDomain_closure_subset hU hu hb hε (frontier_subset_closure hx)
  refine ⟨hh.1,le_antisymm hh.2 ?_⟩
  by_contra hn
  have hxV : x ∈ negativeLevelDomain U u ε := ⟨hh.1,lt_of_not_ge hn⟩
  have hfront := hx
  rw [frontier,(negativeLevelDomain_isOpen hU hu ε).interior_eq] at hfront
  exact hfront.2 hxV

end PowerConvexity
