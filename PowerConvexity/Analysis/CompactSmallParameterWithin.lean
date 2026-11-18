import PowerConvexity.Analysis.CompactSmallParameter

/-! # Compact parameter tubes using continuity only on the true base set -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped Topology
namespace PowerConvexity
variable {P Q : Type*} [TopologicalSpace P] [NormedAddCommGroup Q]

theorem compact_small_parameter_positive_within
    {S : Set P} (hS : IsCompact S) {F : Q × P → ℝ}
    (hF : ∀ x ∈ S, ContinuousWithinAt F (univ ×ˢ S) (0,x))
    (hpos : ∀ x ∈ S, 0 < F (0,x)) :
    ∃ r > 0, ∀ q : Q, ‖q‖ ≤ r → ∀ x ∈ S, 0 < F (q,x) := by
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let G : Q × S → ℝ := fun z => F (z.1,z.2.val)
  have hG (x : S) : ContinuousAt G (0,x) := by
    have hm : Continuous (fun z : Q × S => (z.1,z.2.val)) :=
      continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
    have hh : ContinuousWithinAt G univ (0,x) :=
      (hF x.val x.property).comp (f := fun z : Q × S => (z.1,z.2.val))
        (x := (0,x)) hm.continuousWithinAt
      (show MapsTo (fun z : Q × S => (z.1,z.2.val)) univ (univ ×ˢ S) from
        fun z _ => ⟨mem_univ _,z.2.property⟩)
    exact hh.continuousAt (by simp)
  obtain ⟨r,hr,hh⟩ := compact_small_parameter_positive (K := (univ : Set S)) isCompact_univ
    (fun x _ => hG x) (fun x _ => hpos x.val x.property)
  exact ⟨r,hr,fun q hq x hx => hh q hq ⟨x,hx⟩ (mem_univ _)⟩

theorem compact_small_parameter_pair_within
    {S : Set P} (hS : IsCompact S) {F G : Q × P → ℝ}
    (hF : ∀ x ∈ S, ContinuousWithinAt F (univ ×ˢ S) (0,x))
    (hG : ∀ x ∈ S, ContinuousWithinAt G (univ ×ˢ S) (0,x))
    (hneg : ∀ x ∈ S, F (0,x) < 0) (hpos : ∀ x ∈ S, 0 < G (0,x)) :
    ∃ r > 0, ∀ q : Q, ‖q‖ ≤ r → ∀ x ∈ S, F (q,x) < 0 ∧ 0 < G (q,x) := by
  obtain ⟨r,hr,hN⟩ := compact_small_parameter_positive_within (F := fun z => -F z) hS
    (fun x hx => (hF x hx).neg) (fun x hx => neg_pos.mpr (hneg x hx))
  obtain ⟨s,hs,hP⟩ := compact_small_parameter_positive_within hS hG hpos
  refine ⟨min r s,lt_min hr hs,?_⟩
  intro q hq x hx
  exact ⟨neg_pos.mp (hN q (hq.trans (min_le_left _ _)) x hx),
    hP q (hq.trans (min_le_right _ _)) x hx⟩

end PowerConvexity
