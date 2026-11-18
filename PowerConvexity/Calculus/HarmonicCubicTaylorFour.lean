import PowerConvexity.Calculus.PoissonHessianLipschitzFour
import PowerConvexity.Calculus.HarmonicUniversalQuadraticApproximationFour

/-! # A uniform cubic remainder for the actual harmonic Taylor polynomial -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open Set Filter Metric Matrix
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
local notation "E" => DeGiorgi.AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem classical_harmonic_unitBall_universal_cubic_taylor_four :
    ∃ M > 0, ∃ L > 0, ∀ g : E → ℝ, ContinuousOn g (closedBall 0 1) →
      InnerProductSpace.HarmonicOnNhd g (ball 0 1) →
      (∀ x ∈ closedBall (0 : E) 1, |g x| ≤ 1) →
      IsQuadraticPolynomial (secondTaylorPolynomialZero g) ∧
      (∀ x, (realBlockHessian realDirections imagDirections
        (secondTaylorPolynomialZero g) x).trace=0) ∧
      ‖realHessian g 0‖ ≤ M ∧
      ∀ r : ℝ, 0 < r → r ≤ (1/2 : ℝ) →
        ∀ x ∈ closedBall (0 : E) r,
          |g x-secondTaylorPolynomialZero g x| ≤ L*r^3 := by
  obtain ⟨M,hM,hbound⟩ := classical_harmonic_unitBall_hessian_universal_bound_four
  obtain ⟨L,hL,hLip⟩ := classical_harmonic_unitBall_hessian_universal_lipschitz_four
  refine ⟨M,hM,L,hL,?_⟩
  intro g hgc hg hgb
  have hg0 := (hg 0 (mem_ball_self (by norm_num))).1
  refine ⟨secondTaylorPolynomialZero_isQuadratic hg0,
    harmonic_secondTaylorPolynomialZero_trace_zero_four hg,
    hbound g hgc hg hgb 0 (mem_closedBall_self (by norm_num)),?_⟩
  intro r hr hrh x hx
  have hreg (y : E) (hy : y ∈ closedBall (0 : E) r) : ContDiffAt ℝ 2 g y :=
    (hg y (mem_ball.mpr ((mem_closedBall.mp hy).trans_lt (hrh.trans_lt (by norm_num))))).1
  have hmod (y : E) (hy : y ∈ closedBall (0 : E) r) :
      ‖realHessian g y-realHessian g 0‖ ≤ L*r := by
    have hh := hLip g hgc hg hgb y (closedBall_subset_closedBall hrh hy)
      0 (mem_closedBall_self (by norm_num))
    rw [sub_zero] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left
      (by simpa only [mem_closedBall,dist_zero_right] using hy) hL.le)
  exact (actual_secondTaylor_error_of_hessian_modulus hr (mul_nonneg hL.le hr.le)
    hreg hmod x hx).trans_eq (by ring)

end PowerConvexity
