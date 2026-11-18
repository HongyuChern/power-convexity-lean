import PowerConvexity.Calculus.QuadraticUnitBallEnergy
import PowerConvexity.Analysis.ActualWeakPointwiseL2BoundTwo
import PowerConvexity.Calculus.ActualQuadraticDeterminantBoundsTwo

/-! # Actual quadratic jets controlled by their actual ball L2 norm.
The finite-dimensional norm is the genuine integral norm. This estimates
the polynomial approximants, without assuming classical jets of the weak u.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_quadratic_ball_L2_jet_bound_two {r : ℝ} (hr : 0 < r) :
    ∃ C > 0, ∀ q : E → ℝ, IsQuadraticPolynomial q →
      ∀ hq : MemLp q 2 (volume.restrict (ball (0 : E) r)),
        |q 0| ≤ C*‖hq.toLp q‖ ∧
        ‖fderiv ℝ q 0‖ ≤ C*‖hq.toLp q‖ ∧
        ‖realHessian q 0‖ ≤ C*‖hq.toLp q‖ := by
  have hK := isCompact_closedBall (0 : E) r
  have hKi : (interior (closedBall (0 : E) r)).Nonempty := by
    rw [interior_closedBall (0 : E) hr.ne']
    exact nonempty_ball.mpr hr
  letI := quadraticL2NormedAddCommGroup volume hK hKi
  letI : TopologicalSpace (quadraticSubmodule E) :=
    (quadraticL2NormedAddCommGroup volume hK hKi).toMetricSpace.toUniformSpace.toTopologicalSpace
  letI := quadraticL2InnerProductSpace volume hK hKi
  letI : FiniteDimensional ℝ (quadraticSubmodule E) := quadraticSubmodule_finiteDimensional
  letI : AddCommGroup (quadraticJetSpace E) :=
    (inferInstance : NormedAddCommGroup (quadraticJetSpace E)).toAddCommGroup
  letI : Module ℝ (quadraticJetSpace E) :=
    (inferInstance : NormedSpace ℝ (quadraticJetSpace E)).toModule
  letI : NormedSpace ℝ (quadraticSubmodule E) := InnerProductSpace.toNormedSpace
  letI : AddCommMonoid (quadraticSubmodule E) :=
    (inferInstance : NormedAddCommGroup (quadraticSubmodule E)).toAddCommGroup.toAddCommMonoid
  letI : Module ℝ (quadraticSubmodule E) :=
    (inferInstance : NormedSpace ℝ (quadraticSubmodule E)).toModule
  letI : AddCommMonoid (quadraticJetSpace E) :=
    (inferInstance : NormedAddCommGroup (quadraticJetSpace E)).toAddCommGroup.toAddCommMonoid
  letI : TopologicalSpace (quadraticJetSpace E) :=
    (inferInstance : NormedAddCommGroup (quadraticJetSpace E)).toMetricSpace.toUniformSpace.toTopologicalSpace
  let J : quadraticSubmodule E →L[ℝ] quadraticJetSpace E := {
    toLinearMap := quadraticJetMap
    cont := quadraticL2Jet_continuous volume hK hKi }
  obtain ⟨C,hC,hJ⟩ := ContinuousLinearMap.bound
    (𝕜 := ℝ) (𝕜₂ := ℝ) («E» := quadraticSubmodule E) («F» := quadraticJetSpace E) J
  refine ⟨C,hC,?_⟩
  intro q hqp hq
  let p : quadraticSubmodule E := ⟨q,hqp⟩
  have hn2 : ‖p‖^2 = ‖hq.toLp q‖^2 := by
    rw [quadraticL2_norm_sq volume hK hKi,
      ← quadraticL2Energy_openBall_eq_closedBall volume (0 : E) r]
    exact (actual_scalar_L2_norm_squared_two hq).symm
  have hn : ‖p‖ = ‖hq.toLp q‖ := by
    nlinarith [norm_nonneg p,norm_nonneg (hq.toLp q)]
  have hb : ‖J p‖ ≤ C*‖hq.toLp q‖ := by
    calc
      ‖J p‖ ≤ C*‖p‖ := hJ p
      _ = C*‖hq.toLp q‖ := by rw [hn]
  have he : ‖J p‖ = max |q 0| (max ‖fderiv ℝ q 0‖ ‖realHessian q 0‖) := by
    rfl
  rw [he] at hb
  exact ⟨(le_max_left _ _).trans hb,
    (le_trans (le_max_left _ _) (le_max_right _ _)).trans hb,
    (le_trans (le_max_right _ _) (le_max_right _ _)).trans hb⟩

end PowerConvexity
