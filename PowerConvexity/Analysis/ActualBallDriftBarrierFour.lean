import PowerConvexity.Analysis.ActualZeroTraceAEBarrierFour
import PowerConvexity.Analysis.ActualLocalClassicalDriftWeakFour
import PowerConvexity.Calculus.ClassicalBoundaryNormalTwo

/-! # The actual quadratic ball barrier with its nonzero coefficient divergence -/
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

def actualBallDriftBarrierSourceFour (a : E → Mat) (b : E → E) (c : E) (k : ℝ) (x : E) : ℝ :=
  2*k*((a x).trace+inner ℝ (x-c) (b x))

theorem actual_ball_drift_barrier_equation_four (a : E → Mat) (b : E → E)
    (c x : E) (k r : ℝ) :
    (∑ i, ∑ j, a x i j*euclideanHessian (translatedBallPotential (-k) r c) x i j)+
      fderiv ℝ (translatedBallPotential (-k) r c) x (b x) =
        -actualBallDriftBarrierSourceFour a b c k x := by
  have hH (i j : Fin (2+2)) :
      euclideanHessian (translatedBallPotential (-k) r c) x i j =
        (-2*k)*(if i=j then 1 else 0) := by
    simp only [euclideanHessian,translatedBallPotential_realHessian,
      orthonormal_iff_ite.mp (EuclideanSpace.orthonormal_single (𝕜 := ℝ))]
    ring
  simp only [hH,mul_ite,mul_zero,mul_one,Finset.sum_ite_eq,
    Finset.mem_univ,if_true,translatedBallPotential_fderiv_apply]
  rw [← Finset.sum_mul]
  simp only [actualBallDriftBarrierSourceFour,Matrix.trace,Matrix.diag_apply]
  ring

theorem actual_ball_drift_barrier_source_memLp_four {a : E → Mat} {b : E → E}
    {c : E} {r k : ℝ}
    (ha : ∀ i j, ContinuousOn (fun y => a y i j) (closedBall c r))
    (hb : ContinuousOn b (closedBall c r)) :
    MemLp (actualBallDriftBarrierSourceFour a b c k) 2 (volume.restrict (ball c r)) := by
  apply continuousOn_memLp_two_of_subset_compact measurableSet_ball
    (isCompact_closedBall c r) ball_subset_closedBall
  change ContinuousOn (fun x => 2*k*((∑ i, a x i i)+inner ℝ (x-c) (b x))) (closedBall c r)
  exact continuousOn_const.mul ((continuousOn_finsetSum _ (fun i _ => ha i i)).add
    ((continuousOn_id.sub continuousOn_const).inner hb))

theorem actual_ball_drift_barrier_weak_four {c : E} {r k : ℝ}
    (A : EllipticCoeff (2+2) (ball c r))
    (hA : ∀ i j, ContDiffOn ℝ 1 (fun y => A.a y i j) (ball c r))
    (hAC : ∀ i j, ContinuousOn (fun y => A.a y i j) (closedBall c r))
    {b : E → E} (hb : ContinuousOn b (closedBall c r))
    (hdiv : ∀ x ∈ ball c r, actualCoefficientColumnDivergenceFour A.a x=b x) :
    ActualScalarWeakEquationTwo A (actualBallDriftBarrierSourceFour A.a b c k)
      (translatedBallPotential (-k) r c) := by
  apply actual_local_classical_drift_weak_four isOpen_univ
    (translatedBallPotential_contDiff (-k) r c 2).contDiffOn (subset_univ _) A hA hdiv
    (actual_ball_drift_barrier_source_memLp_four hAC hb)
  intro x _
  exact actual_ball_drift_barrier_equation_four A.a b c x k r

theorem actual_ball_drift_barrier_memH01_four {c : E} {r k : ℝ} (hr : 0 < r) (hk : 0 < k) :
    MemH01 (translatedBallPotential (-k) r c) (ball c r) := by
  apply actual_positive_boundary_barrier_memH01_two isOpen_ball
    (by rw [closure_ball c hr.ne']; exact isCompact_closedBall c r)
    (translatedBallPotential_contDiff (-k) r c 1)
  · intro x hx
    have hn : ‖x-c‖ < r := by simpa only [mem_ball,dist_eq_norm] using hx
    change 0 < (-k)*(‖x-c‖^2-r^2)
    have hh : ‖x-c‖^2 < r^2 := sq_lt_sq₀ (norm_nonneg _) hr.le |>.mpr hn
    nlinarith
  · intro x hx
    rw [frontier_ball c hr.ne'] at hx
    exact translatedBallPotential_zero_on_sphere (-k) r c x
      (by simpa only [mem_sphere,dist_eq_norm] using hx)

theorem actual_ball_drift_barrier_source_lower_four {a : E → Mat} {b : E → E}
    {c x : E} {r k : ℝ} (hk : 0 ≤ k) (hx : x ∈ ball c r)
    (htrace : 1 ≤ (a x).trace) (hb : r*‖b x‖ ≤ 1/2) :
    k ≤ actualBallDriftBarrierSourceFour a b c k x := by
  have hn : ‖x-c‖ ≤ r := (show ‖x-c‖ < r from by simpa only [mem_ball,dist_eq_norm] using hx).le
  have hi : -(1/2 : ℝ) ≤ inner ℝ (x-c) (b x) := by
    have hh := abs_real_inner_le_norm (x-c) (b x)
    have hm := (mul_le_mul_of_nonneg_right hn (norm_nonneg (b x))).trans hb
    exact (abs_le.mp (hh.trans hm)).1
  dsimp only [actualBallDriftBarrierSourceFour]
  nlinarith

end PowerConvexity
