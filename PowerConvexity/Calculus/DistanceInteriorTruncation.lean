import PowerConvexity.Calculus.InteriorLevelTruncation
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # The frozen distance-to-boundary truncation

This is the manuscript's Omega_epsilon: points of U at distance greater than
epsilon from frontier U. It is distinct from the auxiliary negative-level set.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped Topology ContDiff
namespace PowerConvexity
variable {E : Type*} [MetricSpace E]

noncomputable def distanceInteriorDomain (U : Set E) (ε : ℝ) : Set E :=
  U ∩ {x | ε < infDist x (frontier U)}

theorem distanceInteriorDomain_isOpen {U : Set E} (hU : IsOpen U) (ε : ℝ) :
    IsOpen (distanceInteriorDomain U ε) :=
  hU.inter (isOpen_lt continuous_const (continuous_infDist_pt (frontier U)))

theorem distanceInteriorDomain_closure_subset
    {U : Set E} (hU : IsOpen U) {ε : ℝ} (hε : 0 < ε) :
    closure (distanceInteriorDomain U ε) ⊆ {x | x ∈ U ∧ ε ≤ infDist x (frontier U)} := by
  have hc : IsClosed (closure U ∩ {x | ε ≤ infDist x (frontier U)}) :=
    isClosed_closure.inter (isClosed_le continuous_const (continuous_infDist_pt (frontier U)))
  have hs : distanceInteriorDomain U ε ⊆ closure U ∩ {x | ε ≤ infDist x (frontier U)} :=
    fun x hx => ⟨subset_closure hx.1,(show ε < infDist x (frontier U) from hx.2).le⟩
  have hcl := closure_minimal hs hc
  intro x hx
  have hh := hcl hx
  refine ⟨?_,hh.2⟩
  by_contra hn
  have hxf : x ∈ frontier U := by rw [hU.frontier_eq]; exact ⟨hh.1,hn⟩
  have hd : ε ≤ infDist x (frontier U) := hh.2
  rw [infDist_zero_of_mem hxf] at hd
  exact (not_le_of_gt hε) hd

theorem distanceInteriorDomain_isCompact_closure
    {U : Set E} (hK : IsCompact (closure U)) (ε : ℝ) :
    IsCompact (closure (distanceInteriorDomain U ε)) :=
  hK.of_isClosed_subset isClosed_closure (closure_mono inter_subset_left)

theorem distanceInteriorDomain_frontier_value
    {U : Set E} (hU : IsOpen U) {ε : ℝ} (hε : 0 < ε) :
    ∀ x ∈ frontier (distanceInteriorDomain U ε), x ∈ U ∧ infDist x (frontier U) = ε := by
  intro x hx
  have hh := distanceInteriorDomain_closure_subset hU hε (frontier_subset_closure hx)
  refine ⟨hh.1,le_antisymm ?_ hh.2⟩
  by_contra hn
  have hxV : x ∈ distanceInteriorDomain U ε := ⟨hh.1,lt_of_not_ge hn⟩
  have hfront := hx
  rw [frontier,(distanceInteriorDomain_isOpen hU ε).interior_eq] at hfront
  exact hfront.2 hxV

end PowerConvexity
