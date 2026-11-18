import PowerConvexity.Calculus.SmallCMAQuadraticIterationTwo
import PowerConvexity.Calculus.ActualHessianFromQuadraticApproximationTwo
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Actual small-amplitude CMA Hessian bound at the centre.
The proof combines the actual background iteration with the actual C2 Taylor
limit. No uniform ellipticity, Hessian bound or derivative modulus is assumed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Set Filter Metric Matrix
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
local notation "E" => DeGiorgi.AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_small_CMA_center_Hessian_bound_two :
    ∃ C > 0, ∃ ε₀ > 0, ∀ ε > 0, ε ≤ ε₀ → ∀ w : E → ℝ,
      ContinuousOn w (closedBall 0 1) → ContDiffOn ℝ 2 w (ball 0 1) →
      (∀ x ∈ ball (0 : E) 1, (1+complexHessian realDirections imagDirections w x).PosSemidef) →
      (∀ x ∈ ball (0 : E) 1, (1+complexHessian realDirections imagDirections w x).det = 1) →
      (∀ x ∈ closedBall (0 : E) 1, |w x| ≤ ε) → ‖realHessian w 0‖ ≤ C*ε := by
  obtain ⟨M,hM,r,hr,hr1,ε₀,hε₀,hiter⟩ := actual_small_CMA_quadratic_iteration_two
  refine ⟨2*M,by positivity,ε₀,hε₀,?_⟩
  intro ε hε he w hwc hw hp hd hb
  have hz : (0 : E) ∈ ball 0 1 := mem_ball_self (by norm_num)
  have hw0 : ContDiffAt ℝ 2 w 0 := (hw 0 hz).contDiffAt (isOpen_ball.mem_nhds hz)
  have hδ0 : Tendsto (fun n : ℕ => ε*(1/2 : ℝ)^n) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ)<1))
  apply actual_Hessian_norm_from_quadratic_approximation_two hw0 (by positivity)
    (fun n => r^n) (fun n => ε*(1/2 : ℝ)^n)
    (fun n => pow_pos hr n) (fun n => by positivity)
    (tendsto_pow_atTop_nhds_zero_of_lt_one hr.le hr1) hδ0
  intro n
  obtain ⟨q,hq,_,_,hqH,hqa⟩ := hiter ε hε he w hwc hw hp hd hb n
  refine ⟨q,hq,(hqH 0).trans ?_,hqa⟩
  exact mul_le_of_le_one_right (by positivity) (by
    linarith only [pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) n])

end PowerConvexity
