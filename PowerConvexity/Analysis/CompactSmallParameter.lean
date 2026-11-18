import PowerConvexity.Analysis.ParameterMinimum

/-! # Uniform small parameters on a compact base

The compactness argument is independent of the PDE and does not presume a
uniform spectral gap. It is used to choose one perturbation energy radius.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Metric
open scoped Topology
namespace PowerConvexity
variable {X P : Type*} [TopologicalSpace X] [NormedAddCommGroup P]

theorem compact_small_parameter_positive
    {K : Set X} (hK : IsCompact K) {F : P × X → ℝ}
    (hF : ∀ x ∈ K, ContinuousAt F (0,x))
    (hpos : ∀ x ∈ K, 0 < F (0,x)) :
    ∃ r > 0, ∀ p : P, ‖p‖ ≤ r → ∀ x ∈ K, 0 < F (p,x) := by
  have hev : ∀ᶠ p : P in 𝓝 0, ∀ x ∈ K, 0 < F (p,x) :=
    hK.eventually_forall_of_forall_eventually (fun x hx =>
      (hF x hx).tendsto.eventually (lt_mem_nhds (hpos x hx)))
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨δ/2,by positivity,?_⟩
  intro p hp x hx
  have hm : p ∈ ball 0 δ := by
    rw [mem_ball,dist_zero_right]
    linarith
  exact hball hm x hx

theorem compact_small_parameter_negative
    {K : Set X} (hK : IsCompact K) {F : P × X → ℝ}
    (hF : ∀ x ∈ K, ContinuousAt F (0,x))
    (hneg : ∀ x ∈ K, F (0,x) < 0) :
    ∃ r > 0, ∀ p : P, ‖p‖ ≤ r → ∀ x ∈ K, F (p,x) < 0 := by
  obtain ⟨r,hr,hh⟩ := compact_small_parameter_positive (F := fun z => -F z) hK
    (fun x hx => (hF x hx).neg) (fun x hx => neg_pos.mpr (hneg x hx))
  exact ⟨r,hr,fun p hp x hx => neg_pos.mp (hh p hp x hx)⟩

theorem compact_small_parameter_pair
    {K : Set X} (hK : IsCompact K) {F G : P × X → ℝ}
    (hF : ∀ x ∈ K, ContinuousAt F (0,x)) (hG : ∀ x ∈ K, ContinuousAt G (0,x))
    (hneg : ∀ x ∈ K, F (0,x) < 0) (hpos : ∀ x ∈ K, 0 < G (0,x)) :
    ∃ r > 0, ∀ p : P, ‖p‖ ≤ r → ∀ x ∈ K, F (p,x) < 0 ∧ 0 < G (p,x) := by
  obtain ⟨r,hr,hFr⟩ := compact_small_parameter_negative hK hF hneg
  obtain ⟨s,hs,hGs⟩ := compact_small_parameter_positive hK hG hpos
  refine ⟨min r s,lt_min hr hs,?_⟩
  intro p hp x hx
  exact ⟨hFr p (hp.trans (min_le_left _ _)) x hx,hGs p (hp.trans (min_le_right _ _)) x hx⟩

end PowerConvexity
