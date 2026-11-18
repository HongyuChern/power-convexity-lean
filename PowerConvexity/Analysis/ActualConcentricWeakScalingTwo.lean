import PowerConvexity.Analysis.ActualScalarWeakScalingTwo

/-! # Actual concentric restrictions, including the initial radius one.
Coefficient deviation is checked on the same rescaled field used by the
actual scalar weak equation, with its spatial factor retained.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)

theorem actual_scalar_weak_restrict_concentric_two
    (A : EllipticCoeff (2+2) (ball (0 : E) 1)) {R : ℝ}
    (hR : 0 < R) (hR1 : R ≤ 1) {f u : E → ℝ}
    (hu : ActualScalarWeakEquationTwo A f u) :
    ActualScalarWeakEquationTwo (A.restrict (ball_subset_ball hR1)) f u := by
  by_cases he : R = 1
  · subst R
    change ActualScalarWeakEquationTwo A f u
    exact hu
  · have hl : R < 1 := lt_of_le_of_ne hR1 he
    exact actual_scalar_weak_restrict_ball_two isOpen_ball hR (closedBall_subset_ball hl) hu

theorem actual_rescaled_coefficient_deviation_two
    (A : EllipticCoeff (2+2) (ball (0 : E) 1)) {R epsilon : ℝ}
    (hR : 0 < R) (hR1 : R ≤ 1) (heps : 0 ≤ epsilon)
    (hA : ∀ x ∈ ball (0 : E) 1, ∀ v : E,
      ‖v-matMulE (A.a x) v‖ ≤ (epsilon*‖x‖)*‖v‖) :
    ∀ z ∈ ball (0 : E) 1, ∀ v : E,
      ‖v-matMulE ((rescaleCoeffToUnitBall hR (A.restrict (ball_subset_ball hR1))).a z) v‖ ≤
        (epsilon*R)*‖v‖ := by
  intro z hz v
  have hz1 : ‖z‖ < 1 := by simpa only [mem_ball,dist_zero_right] using hz
  have hzR : ‖R • z‖ < R := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hR]
    nlinarith
  have hzin : R • z ∈ ball (0 : E) 1 := by
    rw [mem_ball,dist_zero_right]
    exact hzR.trans_le hR1
  change ‖v-matMulE (A.a ((0 : E)+R • z)) v‖ ≤ _
  rw [zero_add]
  exact (hA _ hzin v).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hzR.le heps) (norm_nonneg v))

theorem actual_rescaled_coefficient_deviation_ae_two
    (A : EllipticCoeff (2+2) (ball (0 : E) 1)) {R epsilon : ℝ}
    (hR : 0 < R) (hR1 : R ≤ 1) (heps : 0 ≤ epsilon)
    (hA : ∀ x ∈ ball (0 : E) 1, ∀ v : E,
      ‖v-matMulE (A.a x) v‖ ≤ (epsilon*‖x‖)*‖v‖) :
    ∀ᵐ z ∂volume.restrict (ball (0 : E) 1), ∀ v : E,
      ‖v-matMulE ((rescaleCoeffToUnitBall hR (A.restrict (ball_subset_ball hR1))).a z) v‖ ≤
        epsilon*‖v‖ := by
  filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
  intro v
  exact (actual_rescaled_coefficient_deviation_two A hR hR1 heps hA z hz v).trans
    (mul_le_mul_of_nonneg_right (by nlinarith [mul_le_mul_of_nonneg_left hR1 heps])
      (norm_nonneg v))

end PowerConvexity
