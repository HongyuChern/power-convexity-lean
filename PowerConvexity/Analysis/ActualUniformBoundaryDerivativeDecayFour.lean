import PowerConvexity.Analysis.ActualUniformQuotientPowerInterpolationFour

/-! # Actual near-boundary derivative decay from a common affine remainder

The interior ball is the genuine geometric ball. Its ratio to the distance
from the boundary base point is explicit, so all constants can precede the
response and the base point.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace PowerConvexity
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem actual_boundary_derivative_decay_four
    {U : Set V} {u : V → ℝ} {c x : V} {L : V →L[ℝ] ℝ}
    {r R K M H alpha beta : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hK : 0 ≤ K) (hM : 0 ≤ M) (hH : 0 ≤ H) (ha : 0 < alpha) (hb : 0 < beta)
    (hball : ball x r ⊆ U) (hnear : ‖x-c‖ ≤ K*r) (hsmall : (K+1)*r < R)
    (hu : ∀ z ∈ ball x r, DifferentiableAt ℝ u z)
    (herr : ∀ z ∈ U, ‖z-c‖ < R →
      |u z-(u c+L (z-c))| ≤ M*‖z-c‖*‖z-c‖^alpha)
    (hmod : ∀ z ∈ ball x r,
      ‖fderiv ℝ u z-fderiv ℝ u x‖ ≤ H*(‖z-x‖/r)^beta) :
    ‖fderiv ℝ u x-L‖ ≤
      (4*(M*(K+1)*(K+1)^alpha)+H)*r^(alpha*beta/(1+beta)) := by
  have hkp : 0 < K+1 := by linarith
  have hC : 0 ≤ M*(K+1)*(K+1)^alpha := by positivity
  have hvalue : ∀ z ∈ ball x r,
      |u z-((u c+L (x-c))+L (z-x))| ≤ (M*(K+1)*(K+1)^alpha)*r*r^alpha := by
    intro z hz
    have hzx : ‖z-x‖ < r := by simpa only [mem_ball,dist_eq_norm] using hz
    have hzc : ‖z-c‖ ≤ (K+1)*r := by
      have hh := norm_add_le (z-x) (x-c)
      rw [sub_add_sub_cancel] at hh
      nlinarith
    have hid : (u c+L (x-c))+L (z-x)=u c+L (z-c) := by
      rw [add_assoc,show L (x-c)+L (z-x)=L (z-c) by rw [← map_add]; congr 1; abel]
    rw [hid]
    calc
      _ ≤ M*‖z-c‖*‖z-c‖^alpha := herr z (hball hz) (hzc.trans_lt hsmall)
      _ ≤ M*((K+1)*r)*((K+1)*r)^alpha :=
        mul_le_mul (mul_le_mul_of_nonneg_left hzc hM)
          (Real.rpow_le_rpow (norm_nonneg _) hzc ha.le) (by positivity) (by positivity)
      _ = _ := by rw [Real.mul_rpow hkp.le hr.le]; ring
  exact actual_derivative_power_interpolation_four hC hH ha hb hr hr1 hu hvalue hmod

end PowerConvexity
