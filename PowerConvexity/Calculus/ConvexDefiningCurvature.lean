import PowerConvexity.Calculus.ClassicalDefiningLeviTwo
import PowerConvexity.Calculus.LinearProjectionJetBounds

/-! # Nonnegative real tangent curvature from actual convex domain geometry

This uses the genuine local boundary chart and the supporting functional of
the convex set. It yields nonnegativity, with no strict real-curvature claim.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Filter
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem definingFunction_tangent_hessian_nonneg_of_convex
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) {x : E} (hx : x ∈ frontier U)
    {f : E → ℝ} (hf : ContDiffAt ℝ 2 f x) (hfx : f x = 0)
    (hDf : fderiv ℝ f x ≠ 0) (hdef : ∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0)
    (v : E) (hv : fderiv ℝ f x v = 0) : 0 ≤ realHessian f x v v := by
  let l := fderiv ℝ f x
  have hsU : U ⊆ {y : E | l (y-x) ≤ 0} :=
    definingFunction_support_nonpos hU hconv (frontier_subset_closure hx)
      (hf.differentiableAt (by norm_num)) hfx hdef
  have hclosed : IsClosed {y : E | l (y-x) ≤ 0} := by
    apply isClosed_le _ continuous_const
    fun_prop
  have hs := closure_minimal hsU hclosed
  obtain ⟨γ,N,hN,h0N,hγ0,hγ,hγb,hγf,hγD⟩ :=
    exists_contDiff_defining_boundary_chart hU hf hfx hDf hdef
  have hγc := hγ.contDiffAt (hN.mem_nhds h0N)
  have hmax : IsLocalMax (fun y => l (γ y)) (0 : E) := by
    change ∀ᶠ y in 𝓝 (0 : E), l (γ y) ≤ l (γ 0)
    filter_upwards [hN.mem_nhds h0N] with y hy
    rw [hγ0]
    have hh := hs (frontier_subset_closure (hγb hy))
    change l (γ y-x) ≤ 0 at hh
    simpa only [map_sub,sub_nonpos] using hh
  have hnonpos := realHessian_nonpos_of_isLocalMax
    (l.contDiff.contDiffAt.comp 0 hγc) hmax v
  simp only [Function.comp_def] at hnonpos
  rw [realHessian_linear_projection_eq hγc l] at hnonpos
  change l (fderiv ℝ (fderiv ℝ γ) 0 v v) ≤ 0 at hnonpos
  have hz : f ∘ γ =ᶠ[𝓝 (0 : E)] (0 : E → ℝ) := by
    filter_upwards [hN.mem_nhds h0N] with y hy
    exact hγf y hy
  have hchain := realHessian_of_locally_zero_composition
    (show ContDiffAt ℝ 2 f (γ 0) by rwa [hγ0]) hγc hz v v
  rw [hγ0,hγD v hv] at hchain
  change fderiv ℝ f x (fderiv ℝ (fderiv ℝ γ) 0 v v) ≤ 0 at hnonpos
  linarith

end PowerConvexity
