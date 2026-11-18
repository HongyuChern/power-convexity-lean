import PowerConvexity.Analysis.ActualSmoothScalarFluxTwo
import PowerConvexity.Analysis.ActualQuadraticSourceBoundTwo

/-! # Actual weak equations from classical functions on a neighbourhood of a ball

The function is not extended across the original domain boundary. The witness
uses only its actual values and first derivatives on the interior ball.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators ENNReal InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)

def actualLocalClassicalBallWitnessTwo
    {V : Set E} (hV : IsOpen V) {p : E → ℝ} (hp : ContDiffOn ℝ 1 p V)
    {c : E} {r : ℝ} (hclosed : closedBall c r ⊆ V) :
    MemW1pWitness 2 p (ball c r) where
  memLp := continuousOn_memLp_two_of_subset_compact measurableSet_ball
    (isCompact_closedBall c r) ball_subset_closedBall (hp.continuousOn.mono hclosed)
  weakGrad := smoothGradField p
  weakGrad_component_memLp := by
    intro i
    exact continuousOn_memLp_two_of_subset_compact measurableSet_ball
      (isCompact_closedBall c r) ball_subset_closedBall
      (((hp.fderiv_of_isOpen hV (m := 0) (by norm_num)).continuousOn.clm_apply
        (continuousOn_const : ContinuousOn (fun _ : E => EuclideanSpace.single i (1 : ℝ)) V)).mono hclosed)
  isWeakGrad := by
    intro i
    simpa only [smoothGradField,PiLp.toLp_apply] using
      hasWeakPartialDeriv_of_contDiffOn isOpen_ball (hp.mono (ball_subset_closedBall.trans hclosed)) i

theorem actual_local_classical_scalar_weak_two
    {V : Set E} (hV : IsOpen V) {p : E → ℝ} (hp : ContDiffOn ℝ 2 p V)
    {c : E} {r : ℝ} (hclosed : closedBall c r ⊆ V)
    (A : EllipticCoeff (2+2) (ball c r))
    (hA : ∀ i j, ContDiffOn ℝ 1 (fun y => A.a y i j) (ball c r))
    (hdiv : ∀ x ∈ ball c r, ∀ j,
      (∑ i, fderiv ℝ (fun y => A.a y i j) x (EuclideanSpace.single i 1)) = 0)
    {f : E → ℝ} (hf : MemLp f 2 (volume.restrict (ball c r)))
    (hpde : ∀ x ∈ ball c r, (∑ i, ∑ j, A.a x i j*euclideanHessian p x i j) = -f x) :
    ActualScalarWeakEquationTwo A f p := by
  have hsub : ball c r ⊆ V := ball_subset_closedBall.trans hclosed
  let F : E → E := fun y => matMulE (A.a y) (smoothGradField p y)
  have hF (i : Fin (2+2)) : ContDiffOn ℝ 1 (fun y => F y i) (ball c r) := by
    intro x hx
    apply ContDiffAt.contDiffWithinAt
    change ContDiffAt ℝ 1
      (fun y => ∑ j, A.a y i j*fderiv ℝ p y (EuclideanSpace.single j 1)) x
    apply ContDiffAt.sum
    intro j _
    exact ((hA i j).contDiffAt (isOpen_ball.mem_nhds hx)).mul
      (((hp.contDiffAt (hV.mem_nhds (hsub hx))).fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const)
  apply actual_scalar_weak_of_classical_flux_two isOpen_ball isBounded_ball A
    (actualLocalClassicalBallWitnessTwo hV (hp.of_le (by norm_num)) hclosed)
    (Filter.Eventually.of_forall (fun _ => rfl)) hf hF
  · intro x hx
    rfl
  · intro x hx
    rw [show F = fun y => matMulE (A.a y) (smoothGradField p y) by rfl,
      classicalDivergence_matMulE_gradient
        (fun i j => ((hA i j).contDiffAt (isOpen_ball.mem_nhds hx)).differentiableAt (by norm_num))
        (hp.contDiffAt (hV.mem_nhds (hsub hx))) (hdiv x hx)]
    change -(∑ i, ∑ j, A.a x i j*euclideanHessian p x i j) = f x
    rw [hpde x hx,neg_neg]

theorem actual_ball_L2_norm_bound_of_pointwise_two
    {p : E → ℝ} {c : E} {r M : ℝ}
    (hp : MemLp p 2 (volume.restrict (ball c r))) (hM : 0 ≤ M)
    (hb : ∀ x ∈ ball c r, |p x| ≤ M) :
    ‖hp.toLp p‖ ≤ Real.sqrt (M^2*(volume (ball (0 : E) r)).toReal) := by
  letI : IsFiniteMeasure (volume.restrict (ball c r)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hh := actual_scalar_L2_squared_bound_of_ae_bound_two hp hM (by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact hb x hx)
  apply Real.le_sqrt_of_sq_le
  have he : volume (ball c r) = volume (ball (0 : E) r) := by
    exact Measure.addHaar_ball_center volume c r
  simpa only [he] using hh

end PowerConvexity
