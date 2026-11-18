import PowerConvexity.Analysis.ActualClassicalDriftFluxFour
import PowerConvexity.Analysis.ActualLocalClassicalWeakTwo

/-! # Actual scalar fluxes with their full column-divergence term -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
local notation "Mat" => Matrix (Fin (2+2)) (Fin (2+2)) ℝ
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_local_classical_drift_weak_four
    {V : Set E} (hV : IsOpen V) {p : E → ℝ} (hp : ContDiffOn ℝ 2 p V)
    {c : E} {r : ℝ} (hclosed : closedBall c r ⊆ V)
    (A : EllipticCoeff (2+2) (ball c r))
    (hA : ∀ i j, ContDiffOn ℝ 1 (fun y => A.a y i j) (ball c r))
    {b : E → E} (hdiv : ∀ x ∈ ball c r, actualCoefficientColumnDivergenceFour A.a x = b x)
    {f : E → ℝ} (hf : MemLp f 2 (volume.restrict (ball c r)))
    (hpde : ∀ x ∈ ball c r, (∑ i, ∑ j, A.a x i j*euclideanHessian p x i j) + fderiv ℝ p x (b x) = -f x) :
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
      actual_classical_divergence_with_drift_four
        (fun i j => ((hA i j).contDiffAt (isOpen_ball.mem_nhds hx)).differentiableAt (by norm_num))
        (hp.contDiffAt (hV.mem_nhds (hsub hx))),hdiv x hx]
    change -((∑ i, ∑ j, A.a x i j*euclideanHessian p x i j)+fderiv ℝ p x (b x)) = f x
    rw [hpde x hx,neg_neg]

end PowerConvexity
