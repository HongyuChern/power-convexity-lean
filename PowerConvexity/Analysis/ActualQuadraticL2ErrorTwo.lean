import PowerConvexity.Analysis.ActualWeakPointwiseL2BoundTwo

/-! # Actual L2 error bridges for quadratic improvement.
The norms and integrals below refer to the original functions. The error
bound combines the actual harmonic replacement error and a uniform
approximation error, with the actual measure of the comparison domain.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "F" => AmbientSpace (2+2)

theorem actual_scalar_L2_triangle_difference_two {U : Set F} {u v : F → ℝ}
    (hu : MemLp u 2 (volume.restrict U)) (hv : MemLp v 2 (volume.restrict U))
    (hd : MemLp (fun x => u x-v x) 2 (volume.restrict U)) :
    ‖hv.toLp v‖ ≤ ‖hu.toLp u‖+‖hd.toLp (fun x => u x-v x)‖ := by
  have he : hd.toLp (fun x => u x-v x) = hu.toLp u-hv.toLp v := hu.toLp_sub hv
  rw [he]
  calc
    ‖hv.toLp v‖ = ‖hu.toLp u-(hu.toLp u-hv.toLp v)‖ := by rw [sub_sub_cancel]
    _ ≤ ‖hu.toLp u‖+‖hu.toLp u-hv.toLp v‖ := norm_sub_le _ _

theorem actual_continuous_ball_memLp_two {q : F → ℝ} (hq : Continuous q)
    (c : F) (r : ℝ) : MemLp q 2 (volume.restrict (ball c r)) := by
  letI : IsFiniteMeasure (volume.restrict (ball c r)) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact measure_ball_lt_top⟩
  obtain ⟨C,hC⟩ := (isCompact_closedBall c r).exists_bound_of_continuousOn hq.continuousOn
  apply MemLp.of_bound hq.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  exact hC x (ball_subset_closedBall hx)

theorem actual_quadratic_comparison_square_error_two {U : Set F}
    [IsFiniteMeasure (volume.restrict U)] {u v q : F → ℝ}
    (hu : MemLp u 2 (volume.restrict U)) (hv : MemLp v 2 (volume.restrict U))
    (hq : MemLp q 2 (volume.restrict U)) {a : ℝ} (ha : 0 ≤ a)
    (herror : ∀ᵐ x ∂volume.restrict U, |v x-q x| ≤ a) :
    (∫ x in U, (u x-q x)^2) ≤
      2*‖(hu.sub hv).toLp (fun x => u x-v x)‖^2+2*a^2*(volume U).toReal := by
  have hdiffI : Integrable (fun x => (u x-v x)^2) (volume.restrict U) :=
    (hu.sub hv).integrable_sq
  have htargetI : Integrable (fun x => (u x-q x)^2) (volume.restrict U) :=
    (hu.sub hq).integrable_sq
  have hboundI : Integrable (fun x => 2*(u x-v x)^2+2*a^2) (volume.restrict U) :=
    (hdiffI.const_mul 2).add (integrable_const _)
  have hi := integral_mono_ae htargetI hboundI (by
    filter_upwards [herror] with x hx
    have hh : (v x-q x)^2 ≤ a^2 := by
      nlinarith [sq_abs (v x-q x),abs_nonneg (v x-q x)]
    nlinarith [sq_nonneg ((u x-v x)-(v x-q x))])
  have hn : ‖(hu.sub hv).toLp (fun x => u x-v x)‖^2 = ∫ x in U, (u x-v x)^2 :=
    actual_scalar_L2_norm_squared_two (u := fun x => u x-v x) (hu.sub hv)
  rw [integral_add (hdiffI.const_mul 2) (integrable_const (2*a^2)),integral_const_mul,← hn] at hi
  simpa only [integral_const,Measure.real,Measure.restrict_apply_univ,smul_eq_mul,mul_comm] using hi

end PowerConvexity
