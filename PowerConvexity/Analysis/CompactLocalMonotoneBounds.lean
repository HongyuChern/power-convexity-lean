import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.Real.Lemmas

/-! # A single numerical bound from local bounds on a compact parameter set -/
set_option autoImplicit false
open Set Filter
open scoped Topology
namespace PowerConvexity
variable {X : Type*} [TopologicalSpace X]

theorem compact_uniform_monotone_bound_of_local
    {K : Set X} (hK : IsCompact K) (P : X → ℝ → Prop)
    (hmono : ∀ x a b, a ≤ b → P x a → P x b)
    (hlocal : ∀ x ∈ K, ∃ M ≥ 0, ∀ᶠ y in 𝓝 x, P y M) :
    ∃ M ≥ 0, ∀ x ∈ K, P x M := by
  let Q : Set X → Prop := fun S => ∃ M ≥ 0, ∀ x ∈ S, P x M
  apply hK.induction_on (p := Q)
  · exact ⟨0,le_rfl,fun x hx => False.elim (notMem_empty x hx)⟩
  · intro S T hST hT
    obtain ⟨M,hM,hMT⟩ := hT
    exact ⟨M,hM,fun x hx => hMT x (hST hx)⟩
  · intro S T hS hT
    obtain ⟨M,hM,hMS⟩ := hS
    obtain ⟨N,hN,hNT⟩ := hT
    refine ⟨max M N,hM.trans (le_max_left _ _),?_⟩
    intro x hx
    rcases hx with hx | hx
    · exact hmono x M (max M N) (le_max_left _ _) (hMS x hx)
    · exact hmono x N (max M N) (le_max_right _ _) (hNT x hx)
  · intro x hx
    obtain ⟨M,hM,hnear⟩ := hlocal x hx
    exact ⟨{y | P y M},mem_nhdsWithin_of_mem_nhds hnear,M,hM,fun y hy => hy⟩

end PowerConvexity
