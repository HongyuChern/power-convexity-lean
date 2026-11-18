import PowerConvexity.Analysis.ActualContinuousDomainBoundaryDataFour
import PowerConvexity.Analysis.ActualLocalClassicalWeakTwo

/-! # Uniform actual interior jets at a fixed distance from the boundary -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_continuous_domain_interior_holder_four
    {r lam Lambda alpha Ka Kf F B : ℝ}
    (hr : 0 < r) (hlam : 0 < lam) (hLambda : 0 < Lambda)
    (halpha : 0 < alpha) (halpha1 : alpha < 1) (hKa : 0 ≤ Ka) (hKf : 0 ≤ Kf)
    (hF : 0 ≤ F) (hB : 0 ≤ B) :
    ∃ delta > 0, delta ≤ r/4 ∧ ∃ C ≥ 0,
    ∀ U : Set E, IsOpen U → ∀ D : ActualContinuousDomainLinearDataFour U lam Lambda alpha Ka Kf,
    (∀ x ∈ U, |D.source x| ≤ F) → (∀ x ∈ U, |D.solution x| ≤ B) →
    ∀ x : E, closedBall x (2*r) ⊆ U →
      (|D.solution x| ≤ C ∧ ‖fderiv ℝ D.solution x‖ ≤ C ∧ ‖realHessian D.solution x‖ ≤ C) ∧
      ∀ y ∈ ball x delta,
        ‖realHessian D.solution x-realHessian D.solution y‖ ≤ C*‖x-y‖^alpha := by
  let N₀ := Real.sqrt (B^2*(volume (ball (0 : E) (2*r))).toReal)
  obtain ⟨delta,hd,hd4,C,hC,hscalar⟩ := actual_uniform_scalar_C2_prescribed_holder_interior_two
    hr hlam hLambda hKa hKf hF (Real.sqrt_nonneg _) halpha halpha1
  refine ⟨delta,hd,hd4,C,hC,?_⟩
  intro U hU D hfb hub x hclosed
  have hsub : ball x (2*r) ⊆ U := ball_subset_closedBall.trans hclosed
  have hsmall : closedBall x r ⊆ ball x (2*r) := closedBall_subset_ball (by linarith)
  let A := D.coeff.restrict hsub
  have hf : MemLp D.source 2 (volume.restrict (ball x (2*r))) :=
    continuousOn_memLp_two_of_subset_compact measurableSet_ball (isCompact_closedBall x (2*r))
      ball_subset_closedBall (D.source_continuous.mono hclosed)
  have hw := actual_local_classical_scalar_weak_two hU D.solution_regular hclosed A
    (fun i j => (D.regular i j).mono hsub) (fun z hz j => D.divergence z (hsub hz) j) hf
    (fun z hz => D.equation z (hsub hz))
  let uw := actualLocalClassicalBallWitnessTwo hU (D.solution_regular.of_le (by norm_num)) hclosed
  have hun : ‖uw.memLp.toLp D.solution‖ ≤ N₀ :=
    actual_ball_L2_norm_bound_of_pointwise_two uw.memLp hB (fun z hz => hub z (hsub hz))
  have hc := hscalar x (ball x (2*r)) isOpen_ball isBounded_ball hsmall A D.lower D.upper
    (fun z hz => D.positive z (hsub hz)) (fun i j => (D.regular i j).mono hsub)
    (fun z hz j => D.divergence z (hsub hz) j)
    (fun z hz w hw => D.holder z (subset_closure (hsub (hsmall hz))) w (subset_closure (hsub (hsmall hw))))
    D.source D.solution hf (D.source_continuous.mono hsub)
    (fun z hz w hw => D.source_holder z (subset_closure (hsub hz)) w (subset_closure (hsub hw)))
    (fun z hz => hfb z (hsub hz)) (D.solution_regular.continuousOn.mono hsub) hw uw hun
  exact ⟨hc.2.1 x (mem_ball_self hd),fun y hy => hc.2.2 x (mem_ball_self hd) y hy⟩

end PowerConvexity
