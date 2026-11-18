import PowerConvexity.Analysis.StrictSubharmonicMaximum

/-! # Strict maximum principle with nonpositive boundary values -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem negative_of_positive_contraction_nonpositive_boundary
    {U : Set E} (hU : IsOpen U) (hK : IsCompact (closure U)) {f : E → ℝ}
    (hfc : ContinuousOn f (closure U)) (hf : ContDiffOn ℝ 2 f U)
    (hboundary : ∀ x ∈ frontier U, f x ≤ 0)
    (L : E → (E →L[ℝ] E →L[ℝ] ℝ) →ₗ[ℝ] ℝ)
    (hL : ∀ x ∈ U, HessianPositive (L x))
    (hpos : ∀ x ∈ U, 0 < L x (realHessian f x)) :
    ∀ x ∈ U, f x < 0 := by
  have hno (x : E) (hx : x ∈ U) : ¬ IsLocalMax f x :=
    no_localMax_of_positive_hessian_contraction (hf.contDiffAt (hU.mem_nhds hx))
      (L x) (hL x hx) (hpos x hx)
  have hnonpos (x : E) (hx : x ∈ closure U) : f x ≤ 0 := by
    by_contra hn
    have hxpos : 0 < f x := lt_of_not_ge hn
    obtain ⟨y, hyK, hymax⟩ := hK.exists_isMaxOn ⟨x, hx⟩ hfc
    have hypos : 0 < f y := hxpos.trans_le (hymax hx)
    have hyU : y ∈ U := by
      by_contra hout
      have hyfront : y ∈ frontier U := by
        rw [frontier, hU.interior_eq]
        exact ⟨hyK, hout⟩
      exact (not_lt_of_ge (hboundary y hyfront)) hypos
    exact hno y hyU (hymax.isLocalMax
      (Filter.mem_of_superset (hU.mem_nhds hyU) subset_closure))
  intro x hx
  refine lt_of_le_of_ne (hnonpos x (subset_closure hx)) ?_
  intro he
  have hm : IsLocalMax f x := by
    filter_upwards [hU.mem_nhds hx] with y hy
    rw [he]
    exact hnonpos y (subset_closure hy)
  exact hno x hx hm


end PowerConvexity
