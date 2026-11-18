import PowerConvexity.Analysis.ActualUniformPullbackL2Two

/-! # Actual physical Euclidean balls inside the normalized ellipsoids -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_linear_forward_jacobians_uniform_two (D : ℝ) :
    ∃ J > 0, ∀ G : E ≃L[ℝ] E, ‖G.toContinuousLinearMap‖ ≤ D →
      |(LinearMap.det G.symm.toLinearMap)⁻¹| ≤ J := by
  obtain ⟨J,hJ,hbound⟩ := actual_linear_jacobians_uniform_of_inverse_bound_two D
  refine ⟨J,hJ,?_⟩
  intro G hG
  exact hbound G.symm (by simpa only [G.symm_symm] using hG)

theorem actual_physical_ball_integral_bound_two
    {U : Set E} {h : E → ℝ} (hI : IntegrableOn h U) (hpos : ∀ y, 0 ≤ h y)
    (G : E ≃L[ℝ] E) (c : E) {r s B J : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hs1 : s ≤ 1) (hB : 0 < B)
    (hG : ‖G.symm.toContinuousLinearMap‖ ≤ B)
    (hJ : |(LinearMap.det G.symm.toLinearMap)⁻¹| ≤ J)
    (hclosed : closedBall c (2*r) ⊆ G ⁻¹' U) :
    (∫ y in ball (G c) ((r/B)*s), h y) ≤
      J*r^4*(∫ z in ball (0 : E) s, h (G (c+r • z))) := by
  let S : Set E := G.symm ⁻¹' ball c (r*s)
  have hSU : S ⊆ U := by
    intro y hy
    have hyr : G.symm y ∈ closedBall c (2*r) :=
      (closedBall_subset_closedBall (by nlinarith : r*s ≤ 2*r)) (ball_subset_closedBall hy)
    simpa only [mem_preimage,G.apply_symm_apply] using hclosed hyr
  have hinner : ball (G c) ((r/B)*s) ⊆ S := by
    intro y hy
    change dist (G.symm y) c < r*s
    rw [dist_eq_norm]
    have he : G.symm y-c = G.symm (y-G c) := by simp only [map_sub,G.symm_apply_apply]
    rw [he]
    calc
      ‖G.symm (y-G c)‖ ≤ ‖G.symm.toContinuousLinearMap‖*‖y-G c‖ :=
        G.symm.toContinuousLinearMap.le_opNorm _
      _ ≤ B*‖y-G c‖ := mul_le_mul_of_nonneg_right hG (norm_nonneg _)
      _ < B*((r/B)*s) := mul_lt_mul_of_pos_left (by simpa only [mem_ball,dist_eq_norm] using hy) hB
      _ = r*s := by field_simp
  have hmono : (∫ y in ball (G c) ((r/B)*s), h y) ≤ ∫ y in S, h y :=
    setIntegral_mono_set (hI.mono_set hSU) (Eventually.of_forall hpos)
      (Eventually.of_forall (fun y hy => hinner hy))
  have hlin : (∫ y in S, h y) =
      |(LinearMap.det G.symm.toLinearMap)⁻¹| * (∫ z in ball c (r*s), h (G z)) := by
    simpa only [S,G.apply_symm_apply] using
      actual_setIntegral_linear_pullback_two (U := ball c (r*s)) G.symm (fun z => h (G z))
  have haff : (∫ z in ball (0 : E) s, h (G (c+r • z))) =
      (r^4)⁻¹*(∫ z in ball c (r*s), h (G z)) := by
    simpa [AmbientSpace] using crossover_integral_comp_affine_ball (x₀ := c) (ρ := s) hr
      (fun z => h (G z))
  have hmul : (∫ z in ball c (r*s), h (G z)) =
      r^4*(∫ z in ball (0 : E) s, h (G (c+r • z))) := by
    rw [haff]
    field_simp
  calc
    _ ≤ ∫ y in S, h y := hmono
    _ = |(LinearMap.det G.symm.toLinearMap)⁻¹| *
        (r^4*(∫ z in ball (0 : E) s, h (G (c+r • z)))) := by rw [hlin,hmul]
    _ ≤ J*(r^4*(∫ z in ball (0 : E) s, h (G (c+r • z)))) :=
      mul_le_mul_of_nonneg_right hJ (mul_nonneg (pow_nonneg hr.le 4) (integral_nonneg (fun z => hpos _)))
    _ = _ := by ring

end PowerConvexity
