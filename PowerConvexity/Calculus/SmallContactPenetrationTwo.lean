import PowerConvexity.Calculus.SmallContactGaussianComparisonTwo

/-! # A genuine lower contact gives a controlled point in the smaller ball.
The Gaussian is an actual smooth barrier. Its minimum is attained on the
same compact ball and is excluded from the boundary and the annulus.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
local notation "E" => DeGiorgi.AmbientSpace (2+2)

theorem normalizedContactGaussianTwo_zero_on_sphere (k r : ℝ) (c x : E)
    (hx : ‖x-c‖ = r) : normalizedContactGaussianTwo k r c x = 0 := by
  rw [normalizedContactGaussianTwo,annularBarrier_zero_on_sphere _ _ _ _ hx,mul_zero]

theorem normalizedContactGaussianTwo_pos_inside
    {k r : ℝ} (hk : 0 < k) (hr : 0 < r) {c x : E} (hx : ‖x-c‖ < r) :
    0 < normalizedContactGaussianTwo k r c x := by
  have hsq : ‖x-c‖^2 < r^2 := (sq_lt_sq₀ (norm_nonneg _) hr.le).mpr hx
  have hp : 0 < k/r^2 := div_pos hk (sq_pos_of_pos hr)
  have he : -(k/r^2)*r^2 < -(k/r^2)*‖x-c‖^2 := by
    have hh := mul_lt_mul_of_pos_left hsq hp
    linarith only [hh]
  unfold normalizedContactGaussianTwo annularBarrier radialGaussian
  exact mul_pos (by positivity) (sub_pos.mpr (Real.exp_lt_exp.mpr he))

theorem normalizedContactGaussianTwo_uniform_upper
    {r : ℝ} (hr : 0 < r) (c x : E) :
    normalizedContactGaussianTwo 4096 r c x ≤ r^2*Real.exp 4096 := by
  have hg : radialGaussian (4096/r^2) c x ≤ 1 := by
    unfold radialGaussian
    have hh : -(4096/r^2)*‖x-c‖^2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (sq_nonneg _)
    simpa only [Real.exp_zero] using (Real.exp_le_exp.mpr hh)
  have hb := (annularBarrier_le_gaussian (4096/r^2) r c x).trans hg
  unfold normalizedContactGaussianTwo
  have h := mul_le_mul_of_nonneg_left hb
    (by positivity : 0 ≤ (r^2/(2*4096))*Real.exp 4096)
  have hp : 0 ≤ r^2*Real.exp (4096 : ℝ) := by positivity
  nlinarith only [h,hp]

theorem small_lower_contact_penetration_two
    {w : E → ℝ} {x0 y x1 : E} {a r : ℝ}
    (ha : 0 < a) (hr : 0 < r) (hsmall : a ≤ (1+Real.exp 4096)⁻¹)
    (hwc : ContinuousOn w (closedBall x0 r)) (hw : ContDiffOn ℝ 2 w (ball x0 r))
    (hdet : ∀ x ∈ ball x0 r, (1+complexHessian realDirections imagDirections w x).det = 1)
    (hbelow : ∀ x ∈ closedBall x0 r, -translatedBallPotential (a/2) 0 y x ≤ w x)
    (hx1 : x1 ∈ ball x0 r) (htouch : w x1 = -translatedBallPotential (a/2) 0 y x1) :
    ∃ z ∈ ball x0 (r/16),
      w z+translatedBallPotential (a/2) 0 y z ≤ Real.exp 4096*a*r^2 := by
  let B : E → ℝ := bumpedLowerParaboloidTwo a 4096 r x0 y
  have hBc : Continuous B := (bumpedLowerParaboloidTwo_contDiff a 4096 r x0 y 0).continuous
  obtain ⟨z,hz,hm⟩ := (isCompact_closedBall x0 r).exists_isMinOn
    ⟨x0,mem_closedBall_self hr.le⟩ (hwc.sub hBc.continuousOn)
  have hxnorm : ‖x1-x0‖ < r := by simpa only [mem_ball,dist_eq_norm] using hx1
  have hbpos := normalizedContactGaussianTwo_pos_inside (by norm_num : (0 : ℝ) < 4096) hr hxnorm
  have hn1 : w x1-B x1 < 0 := by
    dsimp only [B,bumpedLowerParaboloidTwo]
    rw [htouch]
    nlinarith only [mul_pos ha hbpos]
  have hneg : w z-B z < 0 :=
    lt_of_le_of_lt (show w z-B z ≤ w x1-B x1 from hm (ball_subset_closedBall hx1)) hn1
  have hznorm : ‖z-x0‖ ≤ r := by simpa only [mem_closedBall,dist_eq_norm] using hz
  have hzball : z ∈ ball x0 r := by
    rw [mem_ball,dist_eq_norm]
    by_contra hh
    have he : ‖z-x0‖ = r := le_antisymm hznorm (le_of_not_gt hh)
    have hBz : B z = -translatedBallPotential (a/2) 0 y z := by
      dsimp only [B,bumpedLowerParaboloidTwo]
      rw [normalizedContactGaussianTwo_zero_on_sphere _ _ _ _ he,mul_zero,add_zero]
    rw [hBz] at hneg
    linarith only [hbelow z hz,hneg]
  have hloc : IsLocalMin (fun x => w x-B x) z :=
    hm.isLocalMin (mem_of_superset (isOpen_ball.mem_nhds hzball) ball_subset_closedBall)
  have hzsmall : z ∈ ball x0 (r/16) := by
    rw [mem_ball,dist_eq_norm]
    by_contra hh
    exact small_contact_gaussian_no_annular_lower_contact_two
      (hw.contDiffAt (isOpen_ball.mem_nhds hzball)) ha hr hsmall
      (hdet z hzball) (le_of_not_gt hh) hznorm hloc
  refine ⟨z,hzsmall,?_⟩
  have hb := mul_le_mul_of_nonneg_left (normalizedContactGaussianTwo_uniform_upper hr x0 z) ha.le
  dsimp only [B,bumpedLowerParaboloidTwo] at hneg
  nlinarith only [hneg,hb]

end PowerConvexity
