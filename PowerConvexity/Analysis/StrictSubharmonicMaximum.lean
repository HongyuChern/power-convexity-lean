import PowerConvexity.Analysis.GradientStrongMinimum

/-! # A strict classical maximum principle on a bounded domain -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ContDiff Topology

namespace PowerConvexity
open CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem no_localMax_of_positive_hessian_contraction {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x)
    (L : (E →L[ℝ] E →L[ℝ] ℝ) →ₗ[ℝ] ℝ) (hL : HessianPositive L)
    (hpos : 0 < L (realHessian f x)) : ¬ IsLocalMax f x := by
  intro hm
  have hn : 0 ≤ L (-realHessian f x) := by
    apply hL
    intro v
    have h := realHessian_nonpos_of_isLocalMax hf hm v
    simpa using h
  rw [map_neg L (realHessian f x)] at hn
  linarith

theorem negative_of_positive_hessian_contraction
    {U : Set E} (hU : IsOpen U) (hK : IsCompact (closure U)) {f : E → ℝ}
    (hfc : ContinuousOn f (closure U)) (hf : ContDiffOn ℝ 2 f U)
    (hboundary : ∀ x ∈ frontier U, f x = 0)
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
      rw [hboundary y hyfront] at hypos
      exact (lt_irrefl 0) hypos
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
