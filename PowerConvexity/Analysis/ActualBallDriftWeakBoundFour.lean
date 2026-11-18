import PowerConvexity.Analysis.ActualBallDriftBarrierFour

/-! # Quadratic bounds for the actual zero-trace weak solution with drift -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_ball_drift_zeroTrace_bound_ae_four {c : E} {r k : ℝ}
    (hr : 0 < r) (hk : 0 < k) (A : EllipticCoeff (2+2) (ball c r))
    (hA : ∀ i j, ContDiffOn ℝ 1 (fun y => A.a y i j) (ball c r))
    (hAC : ∀ i j, ContinuousOn (fun y => A.a y i j) (closedBall c r))
    {b : E → E} (hb : ContinuousOn b (closedBall c r))
    (hdiv : ∀ x ∈ ball c r, actualCoefficientColumnDivergenceFour A.a x=b x)
    (htrace : ∀ x ∈ ball c r, 1 ≤ (A.a x).trace)
    (hsmall : ∀ x ∈ ball c r, r*‖b x‖ ≤ 1/2)
    {f u : E → ℝ} (hf : MemLp f 2 (volume.restrict (ball c r)))
    (hu : ActualScalarWeakEquationTwo A f u) (hu0 : MemH01 u (ball c r))
    (hfb : ∀ᵐ x ∂volume.restrict (ball c r), |f x| ≤ k) :
    ∀ᵐ x ∂volume.restrict (ball c r),
      |u x| ≤ k*(r^2-‖x-c‖^2) ∧ |u x| ≤ k*r^2 := by
  have hgw := actual_ball_drift_barrier_weak_four (k := k) A hA hAC hb hdiv
  have hgz := actual_ball_drift_barrier_memH01_four (c := c) hr hk
  have hfg : ∀ᵐ x ∂volume.restrict (ball c r),
      |f x| ≤ actualBallDriftBarrierSourceFour A.a b c k x := by
    filter_upwards [hfb,ae_restrict_mem measurableSet_ball] with x hx hxb
    exact hx.trans (actual_ball_drift_barrier_source_lower_four hk.le hxb (htrace x hxb) (hsmall x hxb))
  have hh := actual_zeroTrace_scalar_barrier_ae_abs_four isOpen_ball isBounded_ball hf
    (actual_ball_drift_barrier_source_memLp_four hAC hb) hu hgw hu0 hgz hfg
  filter_upwards [hh] with x hx
  have hp : translatedBallPotential (-k) r c x=k*(r^2-‖x-c‖^2) := by
    dsimp only [translatedBallPotential,quadraticBallPotential]
    ring
  rw [hp] at hx
  exact ⟨hx,hx.trans (by nlinarith [sq_nonneg ‖x-c‖])⟩

end PowerConvexity
