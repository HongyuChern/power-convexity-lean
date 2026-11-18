import PowerConvexity.Analysis.MinimumOnVaryingDomain
import Mathlib.Topology.TietzeExtension

/-! # Minimum continuity from joint continuity on a closed parameter neighborhood

Tietze is applied only to the real scalar field on a closed part of the actual
compact closure graph. It does not extend or replace any PDE solution or jet.
-/
set_option autoImplicit false
open Set Filter
open scoped Topology
namespace PowerConvexity
variable {T X : Type*} [TopologicalSpace T] [T2Space T]
  [TopologicalSpace X] [T2Space X] [NormalSpace (T × X)]

theorem continuousAt_minimum_of_joint_continuity_on_closed_neighborhood
    {V : T → Set X}
    (hVo : IsOpen {p : T × X | p.2 ∈ V p.1})
    (hG : IsCompact {p : T × X | p.2 ∈ closure (V p.1)})
    (hK : ∀ t, IsCompact (closure (V t))) (hne : ∀ t, (V t).Nonempty)
    {s : T} {N : Set T} (hN : IsClosed N) (hsN : N ∈ 𝓝 s)
    {F : T × X → ℝ}
    (hF : ContinuousOn F {p : T × X | p.1 ∈ N ∧ p.2 ∈ closure (V p.1)}) :
    ContinuousAt (fun t => sInf ((fun x => F (t,x)) '' closure (V t))) s := by
  let S : Set (T × X) := {p | p.1 ∈ N ∧ p.2 ∈ closure (V p.1)}
  have hS : IsClosed S := by
    exact (hN.preimage continuous_fst).inter hG.isClosed
  let f : C(S,ℝ) := ⟨fun p => F p.1,hF.restrict⟩
  obtain ⟨g,hg⟩ := f.exists_restrict_eq hS
  have heq (p : T × X) (hp : p ∈ S) : g p = F p := by
    have hh := congrArg (fun k : C(S,ℝ) => k ⟨p,hp⟩) hg
    exact hh
  have hcont : Continuous (fun t => sInf ((fun x => g (t,x)) '' closure (V t))) :=
    continuous_minimum_of_open_graph_compact_closure_graph hVo hG hK hne g.continuous.continuousOn
  apply hcont.continuousAt.congr_of_eventuallyEq
  filter_upwards [hsN] with t ht
  congr 1
  apply Set.image_congr
  intro x hx
  exact (heq (t,x) ⟨ht,hx⟩).symm

end PowerConvexity
