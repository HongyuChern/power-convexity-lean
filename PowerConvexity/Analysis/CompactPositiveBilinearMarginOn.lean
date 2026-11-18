import PowerConvexity.Analysis.CompactPositiveBilinearMargin

/-! # Compact bilinear positivity margin from continuity only on the compact set -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
namespace PowerConvexity
variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [TopologicalSpace X]

theorem compact_positive_bilinear_subtraction_margin_of_continuousOn
    {K : Set X} (hK : IsCompact K)
    (H : X → E →L[ℝ] E →L[ℝ] ℝ) (hH : ContinuousOn H K)
    (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hpos : ∀ x ∈ K, ∀ v : E, v ≠ 0 → 0 < H x v v) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ x ∈ K, ∀ v : E, v ≠ 0 → 0 < (H x-eps • B) v v := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨eps,heps,hmargin⟩ := compact_positive_bilinear_subtraction_margin
    (K := (univ : Set K)) isCompact_univ (fun x : K => H x) hH.domRestrict B
    (fun x _ => hpos x x.property)
  exact ⟨eps,heps,fun x hx => hmargin ⟨x,hx⟩ (mem_univ _)⟩

end PowerConvexity
