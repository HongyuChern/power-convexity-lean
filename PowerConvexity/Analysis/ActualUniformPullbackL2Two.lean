import PowerConvexity.Analysis.ActualCommonFrozenUnitBallTwo
import PowerConvexity.Analysis.ActualWeakL2ScalingTwo
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Uniform actual Jacobians and pullback L2 bounds

Only the original L2 function is integrated. The same common physical radius
and inverse-map norm bound give a uniform normalization amplitude.
-/
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

theorem actual_linear_jacobians_uniform_of_inverse_bound_two (B : ℝ) :
    ∃ J > 0, ∀ G : E ≃L[ℝ] E, ‖G.symm.toContinuousLinearMap‖ ≤ B →
      |(LinearMap.det G.toLinearMap)⁻¹| ≤ J := by
  have hc : Continuous (fun T : E →L[ℝ] E => LinearMap.det T.toLinearMap) :=
    ContinuousLinearMap.continuous_det
  obtain ⟨J,hJ⟩ := (isCompact_closedBall (0 : E →L[ℝ] E) B).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max 1 J,lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro G hG
  have hm : G.symm.toContinuousLinearMap ∈ closedBall (0 : E →L[ℝ] E) B := by
    simpa only [mem_closedBall,dist_zero_right] using hG
  have hd : LinearMap.det G.symm.toLinearMap = (LinearMap.det G.toLinearMap)⁻¹ :=
    LinearEquiv.det_coe_symm G.toLinearEquiv
  rw [← hd]
  have hj := hJ G.symm.toContinuousLinearMap hm
  change ‖LinearMap.det G.symm.toLinearMap‖ ≤ J at hj
  rw [Real.norm_eq_abs] at hj
  exact hj.trans (le_max_right _ _)

theorem actual_affine_linear_pullback_L2_squared_bound_two
    {U : Set E} (G : E ≃L[ℝ] E) (c : E) {r : ℝ} (hr : 0 < r)
    (hclosed : ball c r ⊆ G ⁻¹' U) {J : ℝ}
    (hJ : |(LinearMap.det G.toLinearMap)⁻¹| ≤ J)
    {u : E → ℝ} (hu : MemLp u 2 (volume.restrict U))
    (hv : MemLp (fun z => u (G (c+r • z))) 2 (volume.restrict (ball (0 : E) 1))) :
    ‖hv.toLp (fun z => u (G (c+r • z)))‖^2 ≤
      (r^4)⁻¹*J*‖hu.toLp u‖^2 := by
  have hgu := actual_memLp_linear_pullback_two G hu
  have hmono : (∫ z in ball c r, (u (G z))^2) ≤
      ∫ z in G ⁻¹' U, (u (G z))^2 :=
    setIntegral_mono_set hgu.integrable_sq (Eventually.of_forall (fun _ => sq_nonneg _))
      (Eventually.of_forall (fun z hz => hclosed hz))
  have hchange : (∫ z in ball (0 : E) 1, (u (G (c+r • z)))^2) =
      (r^4)⁻¹*(∫ z in ball c r, (u (G z))^2) := by
    simpa [AmbientSpace] using actual_integral_comp_affine_unitBall_two (x₀ := c) hr
      (fun z => (u (G z))^2)
  rw [actual_scalar_L2_norm_squared_two hv,hchange]
  calc
    _ ≤ (r^4)⁻¹*(∫ z in G ⁻¹' U, (u (G z))^2) :=
      mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = (r^4)⁻¹*(|(LinearMap.det G.toLinearMap)⁻¹| *(∫ z in U, (u z)^2)) := by
      rw [actual_setIntegral_linear_pullback_two G (fun z => (u z)^2)]
    _ ≤ (r^4)⁻¹*(J*(∫ z in U, (u z)^2)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hJ (integral_nonneg (fun _ => sq_nonneg _))) (by positivity)
    _ = _ := by rw [actual_scalar_L2_norm_squared_two hu]; ring

theorem actual_affine_linear_pullback_L2_uniform_two
    {U : Set E} {u : E → ℝ} (hu : MemLp u 2 (volume.restrict U))
    {r : ℝ} (hr : 0 < r) (B : ℝ) :
    ∃ N ≥ 0, ∀ (G : E ≃L[ℝ] E) (c : E),
      ‖G.symm.toContinuousLinearMap‖ ≤ B → ball c r ⊆ G ⁻¹' U →
      ∀ hv : MemLp (fun z => u (G (c+r • z))) 2 (volume.restrict (ball (0 : E) 1)),
        ‖hv.toLp (fun z => u (G (c+r • z)))‖ ≤ N := by
  obtain ⟨J,hJ,hbound⟩ := actual_linear_jacobians_uniform_of_inverse_bound_two B
  refine ⟨Real.sqrt ((r^4)⁻¹*J*‖hu.toLp u‖^2),Real.sqrt_nonneg _,?_⟩
  intro G c hG hsub hv
  apply Real.le_sqrt_of_sq_le
  exact actual_affine_linear_pullback_L2_squared_bound_two G c hr hsub (hbound G hG) hu hv

end PowerConvexity
