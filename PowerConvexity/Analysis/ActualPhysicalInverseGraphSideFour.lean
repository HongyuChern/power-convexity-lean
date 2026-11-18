import PowerConvexity.Analysis.ActualCommonGraphHolderBoundsFour
import PowerConvexity.Analysis.ActualInverseGraphCommonRemainderFour

/-! # Actual interior points have the correct inverse-graph side -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_affine_inverse_coordinate_norm_four
    (G : E ≃L[ℝ] E) (c x : E) {r I : ℝ} (hr : 0 < r)
    (hInv : ‖G.symm.toContinuousLinearMap‖ ≤ I) :
    ‖r⁻¹ • G.symm (x-c)‖ ≤ (I/r)*‖x-c‖ := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
  exact (mul_le_mul_of_nonneg_left
    ((G.symm.toContinuousLinearMap.le_opNorm (x-c)).trans
      (mul_le_mul_of_nonneg_right hInv (norm_nonneg _))) (inv_pos.mpr hr).le).trans_eq (by ring)

theorem actual_original_domain_inverse_graph_side_four
    {U : Set E} {c N : E} (G : E ≃L[ℝ] E) {r : ℝ} (hr : 0 < r)
    {rho : E → ℝ} (hN : ‖N‖=1) (hrho0 : rho 0=0)
    (hrho : ∀ z ∈ closedBall (0 : E) 1, DifferentiableAt ℝ rho z)
    (hD : ∀ z ∈ closedBall (0 : E) 1, ‖fderiv ℝ rho z‖ ≤ 1)
    (hinv : ∀ z : E, ∀ t : ℝ, rho (z+t • N)=rho z)
    (hmap : ∀ z ∈ closedBall (0 : E) 2,
      c+G (r • actualGraphShearFour N rho z) ∈ U ↔ 0 < inner ℝ N z)
    {x : E} (hx : x ∈ U) (hnear : ‖r⁻¹ • G.symm (x-c)‖ ≤ 1) :
    0 < inner ℝ N (actualInverseGraphFour N rho (r⁻¹ • G.symm (x-c))) := by
  let z := r⁻¹ • G.symm (x-c)
  have hz : z ∈ closedBall (0 : E) 1 := mem_closedBall.mpr (by simpa only [dist_zero_right] using hnear)
  have hzero : (0 : E) ∈ closedBall (0 : E) 1 := mem_closedBall_self (by norm_num)
  have hrhov : |rho z| ≤ ‖z‖ := by
    have hh := Convex.norm_image_sub_le_of_norm_fderiv_le hrho hD
      (convex_closedBall (0 : E) 1) hzero hz
    simpa only [hrho0,sub_zero,one_mul,Real.norm_eq_abs] using hh
  have hInvNorm : ‖actualInverseGraphFour N rho z‖ ≤ 2 := by
    have hh : ‖actualInverseGraphFour N rho z‖ ≤ ‖z‖+‖rho z • N‖ := by
      simpa only [actualInverseGraphFour,actualGraphShearFour,neg_smul,sub_eq_add_neg]
        using norm_sub_le z (rho z • N)
    have hn : ‖rho z • N‖=|rho z| := by rw [norm_smul,Real.norm_eq_abs,hN,mul_one]
    rw [hn] at hh
    change ‖z‖ ≤ 1 at hnear
    linarith
  apply (hmap _ (mem_closedBall.mpr (by simpa only [dist_zero_right] using hInvNorm))).mp
  rw [(actual_inverse_graph_inverse_four hinv z).2]
  have hrecover : c+G (r • z)=x := by
    dsimp only [z]
    rw [smul_smul,mul_inv_cancel₀ hr.ne',one_smul,G.apply_symm_apply]
    abel
  rw [hrecover]
  exact hx

end PowerConvexity
