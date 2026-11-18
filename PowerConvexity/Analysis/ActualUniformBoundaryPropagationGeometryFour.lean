import PowerConvexity.Analysis.ActualFlatDriftMatrixStripFour

/-! # One fixed Harnack ball and all nearby tangent balls

The inner quarter balls of the moving tangent balls lie in the half-radius
region of one fixed interior ball. The numerical radii are independent of the
normal and of the tangential center.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
local notation "E" => DeGiorgi.AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_fixed_normal_harnack_ball_maps_four {N : E} (hN : ‖N‖=1)
    {R : ℝ} (hR : 0 < R) (hRs : R ≤ 1/4) :
    closedBall (R • N) (3*R/4) ⊆ actualFlatUpperBallFour N 1 := by
  intro x hx
  have hd : ‖x-R • N‖ ≤ 3*R/4 := by simpa only [mem_closedBall,dist_eq_norm] using hx
  have hp : ‖R • N‖=R := by rw [norm_smul,Real.norm_eq_abs,abs_of_pos hR,hN,mul_one]
  have hn : ‖x‖ ≤ ‖x-R • N‖+R := by
    have hh := norm_add_le (x-R • N) (R • N)
    simpa only [sub_add_cancel,hp] using hh
  have hi : |inner ℝ N (x-R • N)| ≤ 3*R/4 := by
    have hh := abs_real_inner_le_norm N (x-R • N)
    rw [hN,one_mul] at hh
    exact hh.trans hd
  rw [inner_sub_right,inner_smul_right,real_inner_self_eq_norm_sq,hN,one_pow,mul_one,abs_le] at hi
  constructor
  · simpa only [mem_ball,dist_zero_right] using (show ‖x‖ < 1 by linarith)
  · change 0 < inner ℝ N x
    linarith [hi.1]

theorem actual_moving_tangent_closed_ball_maps_four {N c : E} (hN : ‖N‖=1)
    {R : ℝ} (hR : 0 < R) (hRs : R ≤ 1/4)
    (hc : inner ℝ N c=R) (hcP : ‖c-R • N‖ ≤ R/16) :
    closedBall c R ⊆ actualFlatClosedUpperBallFour N 1 := by
  intro x hx
  have hd : ‖x-c‖ ≤ R := by simpa only [mem_closedBall,dist_eq_norm] using hx
  have hp : ‖R • N‖=R := by rw [norm_smul,Real.norm_eq_abs,abs_of_pos hR,hN,mul_one]
  have hn : ‖x‖ ≤ ‖x-c‖+(‖c-R • N‖+R) := by
    have hxnorm := norm_add_le (x-c) c
    have hcnorm := norm_add_le (c-R • N) (R • N)
    simp only [sub_add_cancel,hp] at hxnorm hcnorm
    linarith
  have hi : |inner ℝ N (x-c)| ≤ R := by
    have hh := abs_real_inner_le_norm N (x-c)
    rw [hN,one_mul] at hh
    exact hh.trans hd
  rw [inner_sub_right,hc,abs_le] at hi
  constructor
  · simpa only [mem_closedBall,dist_zero_right] using (show ‖x‖ ≤ 1 by linarith)
  · change 0 ≤ inner ℝ N x
    linarith [hi.1]

theorem actual_moving_tangent_open_ball_maps_four {N c : E} (hN : ‖N‖=1)
    {R : ℝ} (hR : 0 < R) (hRs : R ≤ 1/4)
    (hc : inner ℝ N c=R) (hcP : ‖c-R • N‖ ≤ R/16) :
    ball c R ⊆ actualFlatUpperBallFour N 1 := by
  intro x hx
  have hd : ‖x-c‖ < R := by simpa only [mem_ball,dist_eq_norm] using hx
  have hp : ‖R • N‖=R := by rw [norm_smul,Real.norm_eq_abs,abs_of_pos hR,hN,mul_one]
  have hn : ‖x‖ ≤ ‖x-c‖+(‖c-R • N‖+R) := by
    have hxnorm := norm_add_le (x-c) c
    have hcnorm := norm_add_le (c-R • N) (R • N)
    simp only [sub_add_cancel,hp] at hxnorm hcnorm
    linarith
  have hi : |inner ℝ N (x-c)| < R := by
    have hh := abs_real_inner_le_norm N (x-c)
    rw [hN,one_mul] at hh
    exact hh.trans_lt hd
  rw [inner_sub_right,hc,abs_lt] at hi
  constructor
  · simpa only [mem_ball,dist_zero_right] using (show ‖x‖ < 1 by linarith)
  · change 0 < inner ℝ N x
    linarith [hi.1]

theorem actual_moving_quarter_ball_in_fixed_half_four {N c : E}
    {R : ℝ} (hR : 0 < R) (hcP : ‖c-R • N‖ ≤ R/16) :
    closedBall c (R/4) ⊆ ball (R • N) ((3*R/4)/2) := by
  intro x hx
  have hd : ‖x-c‖ ≤ R/4 := by simpa only [mem_closedBall,dist_eq_norm] using hx
  have hn : ‖x-R • N‖ ≤ ‖x-c‖+‖c-R • N‖ := norm_sub_le_norm_sub_add_norm_sub x c _
  simpa only [mem_ball,dist_eq_norm] using (show ‖x-R • N‖ < (3*R/4)/2 by linarith)

end PowerConvexity
