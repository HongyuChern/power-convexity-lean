import PowerConvexity.Calculus.MinkowskiBoundaryNormalRepresentation

/-! # Actual interior balls supplied by Minkowski addition of a ball.
The original closure point is allowed to lie on its boundary. Openness of
the ball summand removes the closure, so the resulting ball is really in
the open domain, rather than merely in its closure.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Filter Metric
open scoped ContDiff Topology Pointwise
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem minkowski_ball_at_scaled_closure_point
    {U : Set E} {t R : ℝ} (ht1 : t < 1) {x : E} (hx : x ∈ closure U) :
    ball (t • x) ((1-t)*R) ⊆ minkowskiDomain t U (ball (0 : E) R) := by
  have hs : 0 < 1-t := sub_pos.mpr ht1
  have hopen : IsOpen ((1-t) • ball (0 : E) R) := isOpen_ball.smul₀ hs.ne'
  intro z hz
  let b : E := (1-t)⁻¹ • (z-t • x)
  have hb : b ∈ ball (0 : E) R := by
    rw [mem_ball,dist_zero_right]
    dsimp only [b]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hs)]
    rw [inv_mul_eq_div]
    apply (div_lt_iff₀ hs).mpr
    simpa only [mem_ball,dist_eq_norm,mul_comm R (1-t)] using hz
  have he : (1-t) • b+t • x = z := by
    dsimp only [b]
    rw [smul_smul,mul_inv_cancel₀ hs.ne',one_smul,sub_add_cancel]
  rw [minkowskiDomain_eq_smul_add,add_comm,← hopen.add_closure (t • U),closure_smul₀]
  exact ⟨(1-t) • b,⟨b,hb,rfl⟩,t • x,⟨x,hx,rfl⟩,he⟩

theorem minkowski_frontier_actual_tangent_ball [FiniteDimensional ℝ E]
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hboundary : HasC2LocalDefiningFunction U)
    {t R : ℝ} (ht : 0 < t) (ht1 : t < 1) (hR : 0 < R)
    {y : E} (hy : y ∈ frontier (minkowskiDomain t U (ball (0 : E) R))) :
    ∃ c : E, ball c ((1-t)*R) ⊆ minkowskiDomain t U (ball (0 : E) R) ∧
      ‖y-c‖ = (1-t)*R := by
  obtain ⟨x,hx,f,hf,hfx,hDf,hdef,he⟩ :=
    minkowski_frontier_exists_parallel_normal hU hconv hK hboundary ht ht1 hR hy
  refine ⟨t • x,minkowski_ball_at_scaled_closure_point ht1 (frontier_subset_closure hx),?_⟩
  rw [he,definingParallelMap,add_sub_cancel_left,norm_smul,
    Real.norm_eq_abs,abs_of_pos (mul_pos (sub_pos.mpr ht1) hR),
    definingUnitNormal_norm hDf,mul_one]

end PowerConvexity
