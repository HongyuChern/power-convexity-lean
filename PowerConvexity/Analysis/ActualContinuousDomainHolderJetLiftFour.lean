import PowerConvexity.Analysis.ActualContinuousDomainClosureHolderFour
import PowerConvexity.Calculus.ActualHolderC2JetLiftTwo

/-! # The actual original-domain response belongs to the complete Holder jet space -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_continuous_domain_holder_jet_lift_four
    {U : Set E} [CompactSpace (closure U)]
    (hU : IsOpen U) (hK : IsCompact (closure U)) (hproper : U ≠ univ) (hconv : Convex ℝ U)
    {o : E} {rho diameter R lam Lambda alpha Ka Kf F B M T : ℝ}
    (hrho : 0 < rho) (hdia : 0 ≤ diameter) (hR : 0 < R)
    (hlam : 0 < lam) (hLambda : 0 < Lambda) (halpha : 0 < alpha) (halpha1 : alpha < 1)
    (hKa : 0 ≤ Ka) (hKf : 0 ≤ Kf) (hF : 0 ≤ F) (hB : 0 ≤ B) (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hball : closedBall o rho ⊆ U) (hdiam : ∀ c ∈ frontier U, ‖o-c‖ ≤ diameter)
    (D : ActualContinuousDomainLinearDataFour U lam Lambda alpha Ka Kf)
    (hf : ∀ x ∈ U, |D.source x| ≤ F) (hu : ∀ x ∈ U, |D.solution x| ≤ B)
    (hzero : ∀ x ∈ frontier U, D.solution x=0)
    (J : ActualContinuousDomainBoundaryExpansionFour D R M T) :
    ∃ p : actualHolderC2JetSpaceTwo U alpha,
      actualHolderC2JetSpaceTwo_value U alpha p=
        ⟨fun x => D.solution x,D.solution_continuous.domRestrict⟩ := by
  have hfront : IsCompact (frontier U) := hK.of_isClosed_subset isClosed_frontier frontier_subset_closure
  have hGC := (actual_continuous_domain_boundary_polynomial_jets_continuous_four
    hU hconv hrho hdia hR halpha hM hball hdiam D J).1
  have hGbex : ∃ G : ℝ, ∀ c ∈ frontier U, ‖fderiv ℝ (J.polynomial c) c‖ ≤ G :=
    IsCompact.exists_bound_of_continuousOn («E» := E →L[ℝ] ℝ) hfront hGC
  let G : ℝ := Classical.choose hGbex
  have hGb : ∀ c ∈ frontier U, ‖fderiv ℝ (J.polynomial c) c‖ ≤ G := Classical.choose_spec hGbex
  have hconstants := actual_continuous_domain_global_closure_holder_four
    hrho hdia hR hlam hLambda halpha halpha1 hKa hKf hF hB hM hT (le_max_left 0 G)
  let C : ℝ := Classical.choose hconstants
  have hC : 0 ≤ C := (Classical.choose_spec hconstants).1
  have hclosure := (Classical.choose_spec hconstants).2
  have hj := hclosure U hU hproper hconv o hball hdiam D hf hu J
    (fun c hc => (hGb c hc).trans (le_max_right 0 G))
  let Jc := Classical.choose hj
  have hbound := (Classical.choose_spec hj).1
  have hholder := (Classical.choose_spec hj).2
  have hp := actualHolderC2JetSpaceTwo_lift U hU alpha D.solution_regular Jc hzero hC hbound hholder
  exact ⟨Classical.choose hp,(Classical.choose_spec hp).1.1⟩

end PowerConvexity
