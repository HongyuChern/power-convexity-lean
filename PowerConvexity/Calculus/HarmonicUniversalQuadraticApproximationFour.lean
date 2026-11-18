import PowerConvexity.Calculus.PoissonIntegralHessianBoundsFour
import PowerConvexity.Calculus.SecondTaylorHessianModulus

/-! # A uniform quadratic approximation for bounded actual harmonic functions.
The radius is chosen from the actual universal Poisson Hessian modulus before
the harmonic function. The polynomial is its actual Taylor polynomial and has
zero real Laplacian, with a universal actual Hessian norm bound.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open Set Filter Metric Matrix
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
local notation "E" => DeGiorgi.AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE

theorem harmonic_secondTaylorPolynomialZero_trace_zero_four {g : E → ℝ}
    (hg : InnerProductSpace.HarmonicOnNhd g (ball (0 : E) 1)) (x : E) :
    (realBlockHessian realDirections imagDirections (secondTaylorPolynomialZero g) x).trace = 0 := by
  have hzero : (0 : E) ∈ ball 0 1 := mem_ball_self (by norm_num)
  have hH := secondTaylorPolynomialZero_hessian (hg 0 hzero).1 x
  change realBlockTraceFormFour (realHessian (secondTaylorPolynomialZero g) x) = 0
  rw [hH]
  exact actual_classical_harmonic_trace_zero_two hg hzero

theorem classical_harmonic_unitBall_universal_quadratic_approximation_four :
    ∃ M > 0, ∀ η > 0, ∃ r > 0, r ≤ (1/4 : ℝ) ∧
      ∀ g : E → ℝ, ContinuousOn g (closedBall 0 1) →
        InnerProductSpace.HarmonicOnNhd g (ball 0 1) →
        (∀ x ∈ closedBall (0 : E) 1, |g x| ≤ 1) →
        IsQuadraticPolynomial (secondTaylorPolynomialZero g) ∧
        (∀ x, (realBlockHessian realDirections imagDirections (secondTaylorPolynomialZero g) x).trace = 0) ∧
        ‖realHessian g 0‖ ≤ M ∧
        ∀ x ∈ closedBall (0 : E) r, |g x-secondTaylorPolynomialZero g x| ≤ η*r^2 := by
  obtain ⟨M,hM,hHM⟩ := classical_harmonic_unitBall_hessian_universal_bound_four
  refine ⟨M,hM,?_⟩
  intro η hη
  obtain ⟨δ,hδ,hδh,hmod⟩ := classical_harmonic_unitBall_hessian_universal_modulus_four hη
  let r : ℝ := min (δ/2) (1/4)
  have hr : 0 < r := lt_min (half_pos hδ) (by norm_num)
  have hrq : r ≤ (1/4 : ℝ) := min_le_right _ _
  have hrδ : r < δ := (min_le_left _ _).trans_lt (by linarith)
  refine ⟨r,hr,hrq,?_⟩
  intro g hgc hg hgb
  have hzero : (0 : E) ∈ ball 0 1 := mem_ball_self (by norm_num)
  refine ⟨secondTaylorPolynomialZero_isQuadratic (hg 0 hzero).1,
    harmonic_secondTaylorPolynomialZero_trace_zero_four hg,
    hHM g hgc hg hgb 0 (mem_closedBall_self (by norm_num)),?_⟩
  apply actual_secondTaylor_error_of_hessian_modulus hr hη.le
  · intro x hx
    exact (hg x (mem_ball.mpr ((mem_closedBall.mp hx).trans_lt (lt_of_le_of_lt hrq (by norm_num))))).1
  · intro x hx
    apply hmod g hgc hg hgb x
      (closedBall_subset_closedBall (hrq.trans (by norm_num)) hx) 0
      (mem_closedBall_self (by norm_num))
    exact (mem_closedBall.mp hx).trans_lt hrδ

end PowerConvexity
