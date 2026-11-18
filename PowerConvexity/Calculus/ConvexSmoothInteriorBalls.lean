import PowerConvexity.Calculus.DefiningFunctionInteriorBall
import PowerConvexity.Calculus.ScalarBoundaryDecay

/-! # The exact geometric boundary input follows from regular local C2 data

The smooth predicate is regular local C-infinity defining functions, not
positive boundary curvature. Convexity supplies the strict inward normal sign.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open Set Metric
open scoped ContDiff Topology
namespace PowerConvexity

theorem convex_C2_boundary_supported_balls
    {U : Set ℂ} (hU : IsOpen U) (hconv : Convex ℝ U)
    (hboundary : HasC2LocalDefiningFunction U) : HasSupportedInteriorBall U := by
  intro x hx
  obtain ⟨f,hf,hfx,hDf,hdef⟩ := hboundary x hx
  let N := (InnerProductSpace.toDual ℝ ℂ).symm (fderiv ℝ f x)
  have hD (v : ℂ) : fderiv ℝ f x v = inner ℝ N v :=
    InnerProductSpace.toDual_symm_apply.symm
  have hN : N ≠ 0 := by
    intro hn
    apply hDf
    have he := (InnerProductSpace.toDual ℝ ℂ).apply_symm_apply (fderiv ℝ f x)
    change (InnerProductSpace.toDual ℝ ℂ) N = fderiv ℝ f x at he
    rw [hn,map_zero] at he
    exact he.symm
  obtain ⟨r,hr,hball⟩ := exists_interior_ball_of_C2_defining_function hf hfx hN hD hdef
  have hsupport : ∀ y ∈ U, inner ℝ N (y-x) ≤ 0 := by
    intro y hy
    rw [← hD]
    exact definingFunction_support_nonpos hU hconv (frontier_subset_closure hx)
      (hf.differentiableAt (by norm_num)) hfx hdef y hy
  have hstrict := strict_support_of_nonzero_normal hU hN hsupport
  refine ⟨x-r • N,r*‖N‖,mul_pos hr (norm_pos_iff.mpr hN),hball,?_,?_⟩
  · rw [sub_sub_cancel,norm_smul,Real.norm_eq_abs,abs_of_pos hr]
  · intro y hy
    rw [show x-r • N-x = (-r) • N by module,real_inner_smul_left]
    exact mul_pos_of_neg_of_neg (neg_neg_of_pos hr) (hstrict y hy)

theorem convex_smooth_boundary_supported_balls
    {U : Set ℂ} (hU : IsOpen U) (hconv : Convex ℝ U)
    (hboundary : HasSmoothLocalDefiningFunction U) : HasSupportedInteriorBall U :=
  convex_C2_boundary_supported_balls hU hconv (smoothLocalDefiningFunction_implies_C2 hboundary)

end PowerConvexity
