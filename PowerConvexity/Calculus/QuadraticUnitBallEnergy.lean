import PowerConvexity.Calculus.QuadraticL2Geometry
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! # The manuscript's open unit-ball energy equals the compact-ball L2 norm

No change of measure or arbitrary coefficient norm is used. The boundary sphere
has additive Haar measure zero in a nontrivial finite-dimensional real space.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Metric MeasureTheory MeasureTheory.Measure
namespace PowerConvexity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

theorem addHaar_closedBall_ae_ball (μ : Measure E) [IsAddHaarMeasure μ] (c : E) (R : ℝ) :
    closedBall c R =ᵐ[μ] ball c R := by
  apply (ae_eq_of_subset_of_measure_ge ball_subset_closedBall ?_
    measurableSet_ball.nullMeasurableSet measure_closedBall_lt_top.ne).symm
  exact (addHaar_closedBall_eq_addHaar_ball μ c R).le

theorem quadraticL2Energy_openBall_eq_closedBall
    (μ : Measure E) [IsAddHaarMeasure μ] (c : E) (R : ℝ) (q : E → ℝ) :
    quadraticL2Energy μ (ball c R) q = quadraticL2Energy μ (closedBall c R) q := by
  exact setIntegral_congr_set (addHaar_closedBall_ae_ball μ c R).symm

theorem unitClosedBall_interior_nonempty (c : E) : (interior (closedBall c 1)).Nonempty := by
  rw [interior_closedBall c (by norm_num : (1:ℝ) ≠ 0)]
  exact nonempty_ball.mpr (by norm_num)

theorem quadraticL2_norm_sq_openUnitBall
    (μ : Measure E) [IsAddHaarMeasure μ] (c : E) (q : quadraticSubmodule E) :
    letI := quadraticL2NormedAddCommGroup μ (isCompact_closedBall c 1) (unitClosedBall_interior_nonempty c)
    letI : TopologicalSpace (quadraticSubmodule E) :=
      (quadraticL2NormedAddCommGroup μ (isCompact_closedBall c 1)
        (unitClosedBall_interior_nonempty c)).toMetricSpace.toUniformSpace.toTopologicalSpace
    ‖q‖^2 = ∫ x in ball c 1, (q.val x)^2 ∂μ := by
  rw [← quadraticL2Energy,quadraticL2Energy_openBall_eq_closedBall]
  exact quadraticL2_norm_sq μ (isCompact_closedBall c 1) (unitClosedBall_interior_nonempty c) q

theorem pluriharmonicQuadratic_openUnitBall_isCompact
    (μ : Measure E) [IsAddHaarMeasure μ] (c : E) {ι : Type*} (a b : ι → E)
    {ε : ℝ} (hε : 0 ≤ ε) :
    letI := quadraticL2NormedAddCommGroup μ (isCompact_closedBall c 1) (unitClosedBall_interior_nonempty c)
    letI : TopologicalSpace (quadraticSubmodule E) :=
      (quadraticL2NormedAddCommGroup μ (isCompact_closedBall c 1)
        (unitClosedBall_interior_nonempty c)).toMetricSpace.toUniformSpace.toTopologicalSpace
    IsCompact {q : pluriharmonicQuadraticSubmodule a b | ∫ x in ball c 1, (q.val.val x)^2 ∂μ ≤ ε} := by
  letI := quadraticL2NormedAddCommGroup μ (isCompact_closedBall c 1) (unitClosedBall_interior_nonempty c)
  letI : TopologicalSpace (quadraticSubmodule E) :=
    (quadraticL2NormedAddCommGroup μ (isCompact_closedBall c 1)
      (unitClosedBall_interior_nonempty c)).toMetricSpace.toUniformSpace.toTopologicalSpace
  change IsCompact {q : pluriharmonicQuadraticSubmodule a b | quadraticL2Energy μ (ball c 1) q.val.val ≤ ε}
  simp_rw [quadraticL2Energy_openBall_eq_closedBall]
  exact pluriharmonicQuadraticL2Ball_isCompact μ (isCompact_closedBall c 1) (unitClosedBall_interior_nonempty c) a b hε

end PowerConvexity
