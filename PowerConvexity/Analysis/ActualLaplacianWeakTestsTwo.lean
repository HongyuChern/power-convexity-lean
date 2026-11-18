import PowerConvexity.Analysis.CMADeviationLaplacianTwo
import PowerConvexity.Analysis.ActualWeakBallComparison

/-! # Actual classical Laplacian barriers in the full weak test class.
Only local C2 regularity is required; the checked cutoff construction
provides the Sobolev representative on each relatively compact ball.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "F" => AmbientSpace (2+2)

theorem actual_euclidean_trace_eq_block_trace_two (p : F → ℝ) (x : F) :
    (∑ i : Fin (2+2), realHessian p x
      (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) =
      (realBlockHessian realDirections imagDirections p x).trace := by
  rw [← Equiv.sum_comp finSumFinEquiv]
  simp only [Matrix.trace,Matrix.diag_apply,realBlockHessian,blockDirection_eq_single]

theorem actual_local_laplacian_supersolution_two
    {U : Set F} (hU : IsOpen U) {p : F → ℝ} (hp : ContDiffOn ℝ 2 p U)
    (htrace : ∀ x ∈ U, (realBlockHessian realDirections imagDirections p x).trace ≤ 0)
    {c : F} {r R : ℝ} (hr : 0 < r) (hrR : r < R) (hclosed : closedBall c R ⊆ U) :
    IsSupersolution (identityNormalizedEllipticCoeffTwo (ball c r)).1 p := by
  let G : F → F := fun y => matMulE (1 : Matrix (Fin (2+2)) (Fin (2+2)) ℝ)
    (smoothGradField p y)
  have hG (i : Fin (2+2)) : ContDiffOn ℝ 1 (fun x => G x i) U := by
    intro x hx
    have hh := (((hp.contDiffAt (hU.mem_nhds hx)).fderiv_right (m := 1)
      (by norm_num)).clm_apply (contDiffAt_const (c := EuclideanSpace.single i (1 : ℝ))))
    simpa only [G,matMulE_apply,Matrix.one_mulVec,smoothGradField,PiLp.toLp_apply] using
      hh.contDiffWithinAt
  apply supersolution_of_local_classical_flux hU hr hrR hclosed _
    (hp.of_le (by norm_num)) hG
  · intro x hx
    rfl
  · intro x hx
    have hxU := hclosed (closedBall_subset_closedBall hrR.le (ball_subset_closedBall hx))
    have ht : (∑ i : Fin (2+2), realHessian p x
        (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) ≤ 0 := by
      rw [actual_euclidean_trace_eq_block_trace_two]
      exact htrace x hxU
    rw [show G = fun y => matMulE (1 : Matrix (Fin (2+2)) (Fin (2+2)) ℝ)
      (smoothGradField p y) by rfl,
      classicalDivergence_matMulE_gradient
        (A := fun _ : F => (1 : Matrix (Fin (2+2)) (Fin (2+2)) ℝ))
        (fun _ _ => differentiableAt_const _) (hp.contDiffAt (hU.mem_nhds hxU))
        (fun _ => by simp)]
    simpa [Matrix.one_apply,euclideanHessian] using ht

theorem actual_identity_subsolution_restrict_ball_two
    {U : Set F} (hU : IsOpen U) {u : F → ℝ}
    (hu : IsSubsolution (identityNormalizedEllipticCoeffTwo U).1 u)
    {c : F} {r : ℝ} (hr : 0 < r) (hclosed : closedBall c r ⊆ U) :
    IsSubsolution (identityNormalizedEllipticCoeffTwo (ball c r)).1 u := by
  exact hu.restrict_ball hU hr hclosed

end PowerConvexity
