import PowerConvexity.Analysis.MinkowskiBoundaryNeighborhoods

/-! # Uniform neighborhood statements on a compact actual parameter graph -/
set_option autoImplicit false
open Set Filter
open scoped Topology
namespace PowerConvexity

theorem compact_parameter_graph_eventually_subset_joint_open
    {P X : Type*} [TopologicalSpace P] [TopologicalSpace X] [T2Space P]
    {K : Set (P × X)} (hK : IsCompact K) {W : Set (P × X)} (hW : IsOpen W)
    {s : P} (hs : ∀ x : X, (s,x) ∈ K → (s,x) ∈ W) :
    ∀ᶠ t in 𝓝 s, ∀ x : X, (t,x) ∈ K → (t,x) ∈ W := by
  let B := K ∩ Wᶜ
  have hB : IsCompact B := hK.inter_right hW.isClosed_compl
  have hclosed : IsClosed (Prod.fst '' B) := (hB.image continuous_fst).isClosed
  have hsnot : s ∉ Prod.fst '' B := by
    rintro ⟨⟨t,x⟩,⟨hKtx,hWx⟩,hts⟩
    change t = s at hts
    subst t
    exact hWx (hs x hKtx)
  filter_upwards [hclosed.isOpen_compl.mem_nhds hsnot] with t ht
  intro x htx
  by_contra hxW
  exact ht ⟨(t,x),⟨htx,hxW⟩,rfl⟩

theorem compact_parameter_graph_eventually_of_joint_local_property
    {P X : Type*} [TopologicalSpace P] [TopologicalSpace X] [T2Space P]
    {K : Set (P × X)} (hK : IsCompact K) {Q : P × X → Prop} {s : P}
    (hs : ∀ x : X, (s,x) ∈ K → ∀ᶠ p in 𝓝 (s,x), Q p) :
    ∀ᶠ t in 𝓝 s, ∀ x : X, (t,x) ∈ K → Q (t,x) := by
  let W : Set (P × X) := {q | ∀ᶠ p in 𝓝 q, Q p}
  have hWo : IsOpen W := by
    rw [isOpen_iff_mem_nhds]
    intro q hq
    exact hq.eventually_nhds
  filter_upwards [compact_parameter_graph_eventually_subset_joint_open hK hWo hs] with t ht
  intro x hx
  exact (ht x hx).self_of_nhds

theorem compact_parameter_graph_uniform_positive_lower
    {P X : Type*} [TopologicalSpace P] [TopologicalSpace X] [T2Space P]
    {K : Set (P × X)} (hK : IsCompact K) {s : P}
    (hKs : IsCompact {x : X | (s,x) ∈ K}) {g : P × X → ℝ}
    (hg : ∀ x : X, (s,x) ∈ K → ContinuousAt g (s,x))
    (hpos : ∀ x : X, (s,x) ∈ K → 0 < g (s,x)) :
    ∃ eta > 0, ∀ᶠ t in 𝓝 s, ∀ x : X, (t,x) ∈ K → eta ≤ g (t,x) := by
  have hc : ContinuousOn (fun x : X => g (s,x)) {x : X | (s,x) ∈ K} := by
    intro x hx
    exact ((hg x hx).comp (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  obtain ⟨a,ha,haK⟩ := hKs.exists_forall_le' hc hpos
  refine ⟨a/2,half_pos ha,?_⟩
  apply compact_parameter_graph_eventually_of_joint_local_property hK
    (s := s) (Q := fun p => a/2 ≤ g p)
  intro x hx
  have hax : a/2 < g (s,x) := by linarith [haK x hx]
  exact ((hg x hx).tendsto.eventually (lt_mem_nhds hax)).mono (fun _ h => h.le)

end PowerConvexity
