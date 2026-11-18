import PowerConvexity.Calculus.MinkowskiBoundaryNormalRepresentation

/-! # Positive proportionality between actual defining gradients -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Filter
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem regular_defining_derivatives_positive_multiple
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) {x : E} (hx : x ∈ frontier U)
    {f g : E → ℝ} (hf : ContDiffAt ℝ 2 f x) (hfx : f x = 0)
    (hDf : fderiv ℝ f x ≠ 0) (hfdef : ∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0)
    (hg : ContDiffAt ℝ 2 g x) (hgx : g x = 0)
    (hDg : fderiv ℝ g x ≠ 0) (hgdef : ∀ᶠ z in 𝓝 x, z ∈ U ↔ g z < 0) :
    ∃ lam > 0, ∀ v : E, fderiv ℝ g x v = lam*fderiv ℝ f x v := by
  have hsU := definingFunction_support_nonpos hU hconv (frontier_subset_closure hx)
    (hg.differentiableAt (by norm_num)) hgx hgdef
  have hclosed : IsClosed {z : E | fderiv ℝ g x (z-x) ≤ 0} := by
    apply isClosed_le _ continuous_const
    fun_prop
  exact supportingFunctional_positive_defining_multiple hf hfx hDf hfdef
    (fderiv ℝ g x) hDg (closure_minimal hsU hclosed)

end PowerConvexity
