import PowerConvexity.Calculus.ActualSmallCMAHessianBoundTwo
import PowerConvexity.Calculus.IsometricScaledPullbackTwo

/-! # Actual small-CMA estimate on any physical metric ball.
Only an actual fixed-frame isometry is used. There is no assumed derivative
bound, modulus, or change of the domain equation.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Set Metric Matrix
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
local notation "F" => DeGiorgi.AmbientSpace (2+2)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_small_CMA_isometric_ball_Hessian_bound_two :
    ∃ C > 0, ∃ ε₀ > 0, ∀ (L : F ≃ₗᵢ[ℝ] E) (c : E) (r : ℝ), 0 < r →
      ∀ ε > 0, ε ≤ ε₀ → ∀ w : E → ℝ,
      ContinuousOn w (closedBall c r) → ContDiffOn ℝ 2 w (ball c r) →
      (∀ x ∈ ball c r,
        (1+complexHessian (fun i => L (realDirections i)) (fun i => L (imagDirections i)) w x).PosSemidef) →
      (∀ x ∈ ball c r,
        (1+complexHessian (fun i => L (realDirections i)) (fun i => L (imagDirections i)) w x).det = 1) →
      (∀ x ∈ closedBall c r, |w x| ≤ ε*r^2) → ‖realHessian w c‖ ≤ C*ε := by
  obtain ⟨C,hC,ε₀,hε₀,hest⟩ := actual_small_CMA_center_Hessian_bound_two
  refine ⟨C,hC,ε₀,hε₀,?_⟩
  intro L c r hr ε hε he w hwc hw hp hd hb
  obtain ⟨hvc,hv,hvb⟩ := isometricScaledPullbackTwo_local_data L c hr hwc hw hb
  have hmap (x : F) (hx : x ∈ ball 0 1) : c+r • L x ∈ ball c r := by
    rw [mem_ball,isometric_scaled_point_distance_two L c hr]
    exact mul_lt_of_lt_one_right hr (by simpa only [mem_ball,dist_zero_right] using hx)
  have hreg (x : F) (hx : x ∈ ball 0 1) : ContDiffAt ℝ 2 w (c+r • L x) :=
    (hw _ (hmap x hx)).contDiffAt (isOpen_ball.mem_nhds (hmap x hx))
  have hh : ‖realHessian (isometricScaledPullbackTwo L c r w) 0‖ ≤ C*ε := by
    apply hest ε hε he _ hvc hv
    · intro x hx
      rw [isometricScaledPullbackTwo_complexHessian L c hr (hreg x hx)]
      exact hp _ (hmap x hx)
    · intro x hx
      rw [isometricScaledPullbackTwo_complexHessian L c hr (hreg x hx)]
      exact hd _ (hmap x hx)
    · exact hvb
  exact isometricScaledPullbackTwo_recovers_norm L c hr
    ((hw c (mem_ball_self hr)).contDiffAt (isOpen_ball.mem_nhds (mem_ball_self hr)))
    (mul_nonneg hC.le hε.le) hh

end PowerConvexity
