import PowerConvexity.Analysis.ActualCommonFrozenUnitBallTwo

/-! # Uniform actual scalar source control on common physical balls -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_affine_holder_scalar_source_uniform_two
    {U : Set E} {f : E → ℝ} (hf : ContDiffOn ℝ 1 f U)
    {K F D alpha : ℝ} (halpha : 0 < alpha) (hK : 0 ≤ K) (hF : 0 ≤ F) (hD : 0 ≤ D)
    (hLip : ∀ x ∈ U, ∀ y ∈ U, |f x-f y| ≤ K*‖x-y‖^alpha)
    (hbound : ∀ x ∈ U, |f x| ≤ F)
    (G : E ≃L[ℝ] E) (x : E) {r : ℝ} (hr : 0 < r)
    (hG : ‖G.toContinuousLinearMap‖ ≤ D)
    (hclosed : closedBall (G.symm x) (2*r) ⊆ G ⁻¹' U) :
    MemLp (fun z => r^2*f (G (G.symm x+r • z))) 2
        (volume.restrict (ball (0 : E) 1)) ∧
      |r^2*f x| ≤ r^2*F ∧
      ∀ z ∈ ball (0 : E) 1,
        |r^2*f (G (G.symm x+r • z))-r^2*f x| ≤ (r^2*K*(D*r)^alpha)*‖z‖^alpha := by
  have hmaps : MapsTo (fun z => G (G.symm x+r • z)) (ball (0 : E) 2) U := by
    intro z hz
    apply hclosed
    rw [mem_closedBall,dist_eq_norm,add_sub_cancel_left,norm_smul,
      Real.norm_eq_abs,abs_of_pos hr]
    have hz2 : ‖z‖ < 2 := by simpa only [mem_ball,dist_zero_right] using hz
    nlinarith
  have hx : x ∈ U := by
    simpa only [smul_zero,add_zero,G.apply_symm_apply] using
      hmaps (mem_ball_self (by norm_num : (0 : ℝ) < 2))
  have hC : ContDiffOn ℝ 1 (fun z => r^2*f (G (G.symm x+r • z))) (ball (0 : E) 2) :=
    contDiffOn_const.mul (hf.comp (by fun_prop) hmaps)
  have hmem := (actual_C1_scalar_ball_source_growth_two hC).1
  refine ⟨hmem,?_,?_⟩
  · rw [abs_mul,abs_of_nonneg (sq_nonneg r)]
    exact mul_le_mul_of_nonneg_left (hbound x hx) (sq_nonneg r)
  · intro z hz
    have hy := hmaps (ball_subset_ball (by norm_num : (1 : ℝ) ≤ 2) hz)
    have hn : ‖G (G.symm x+r • z)-x‖ ≤ D*r*‖z‖ := by
      rw [map_add,G.apply_symm_apply,add_sub_cancel_left]
      calc
        ‖G (r • z)‖ ≤ ‖G.toContinuousLinearMap‖*‖r • z‖ := G.toContinuousLinearMap.le_opNorm _
        _ ≤ D*‖r • z‖ := mul_le_mul_of_nonneg_right hG (norm_nonneg _)
        _ = _ := by rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr]; ring
    rw [← mul_sub,abs_mul,abs_of_nonneg (sq_nonneg r)]
    exact (mul_le_mul_of_nonneg_left
      ((hLip _ hy x hx).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (norm_nonneg _) hn halpha.le) hK)) (sq_nonneg r)).trans_eq (by
          rw [Real.mul_rpow (mul_nonneg hD hr.le) (norm_nonneg z)]
          ring)

end PowerConvexity
