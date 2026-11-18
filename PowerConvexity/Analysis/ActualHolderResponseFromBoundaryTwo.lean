import PowerConvexity.Analysis.ActualHolderWeakResponseDataTwo
import PowerConvexity.Analysis.ActualContinuousDomainHolderJetLiftFour
import PowerConvexity.Calculus.ActualHolderResponseClosedGraphTwo

/-! # A bounded actual Holder response from actual boundary expansions

Every load is solved by the same complete C0 weak-response operator. The
boundary expansion is the remaining analytic input; even its constants may
depend on the load. The full original-domain Holder jet is proved, and the
closed graph theorem then provides one bounded linear response on the
complete Holder spaces. No Holder-norm density of smooth loads is used.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 1024
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul
attribute [local instance] holderResponseJetSeminormedGroup

theorem actual_holder_response_from_boundary_expansion_two
    {U : Set E} [CompactSpace (closure U)]
    (hU : IsOpen U) (hK : IsCompact (closure U)) (hproper : U ≠ univ) (hconv : Convex ℝ U)
    {o : E} {rho diameter alpha Ka Kd Bd : ℝ}
    (hrho : 0 < rho) (hdia : 0 ≤ diameter)
    (hball : closedBall o rho ⊆ U) (hdiam : ∀ c ∈ frontier U, ‖o-c‖ ≤ diameter)
    (halpha : 0 < alpha) (halpha1 : alpha < 1)
    (hKa : 0 ≤ Ka) (hKd : 0 ≤ Kd) (hBd : 0 ≤ Bd)
    (D : ActualHolderWeakResponseDataTwo U alpha Ka Kd Bd)
    (hexp : ∀ g : actualHolderLoadSpaceTwo (closure U) ℝ alpha,
      ∃ R > 0, ∃ M ≥ 0, ∃ K ≥ 0,
        Nonempty (ActualContinuousDomainBoundaryExpansionFour
          (D.domainData hU hK halpha halpha1 hKa hKd hBd g) R M K)) :
    ∃! S : actualHolderLoadSpaceTwo (closure U) ℝ alpha →L[ℝ] actualHolderC2JetSpaceTwo U alpha,
      (actualHolderC2JetSpaceTwo_value U alpha).comp S=
        D.operator.comp (actualHolderLoadSpaceTwo_value (closure U) ℝ alpha) := by
  apply actual_holder_response_closed_graph_lift_two («E» := E) U hU alpha D.operator
  intro g
  let Q := D.domainData hU hK halpha halpha1 hKa hKd hBd g
  let R : ℝ := Classical.choose (hexp g)
  have hR : 0 < R := (Classical.choose_spec (hexp g)).1
  have hMexist := (Classical.choose_spec (hexp g)).2
  let M : ℝ := Classical.choose hMexist
  have hM : 0 ≤ M := (Classical.choose_spec hMexist).1
  have hKexist := (Classical.choose_spec hMexist).2
  let K : ℝ := Classical.choose hKexist
  have hKb : 0 ≤ K := (Classical.choose_spec hKexist).1
  have hJ := (Classical.choose_spec hKexist).2
  let J : ActualContinuousDomainBoundaryExpansionFour Q R M K := Classical.choice hJ
  have hb := D.domainData_bounds hU hK halpha halpha1 hKa hKd hBd g
  have hf := hb.1
  have hu := hb.2.1
  have hzero := hb.2.2
  change (∀ x ∈ closure U, |Q.source x| ≤ Bd*‖g‖) at hf
  change (∀ x ∈ closure U, |Q.solution x| ≤ ‖D.operator‖*‖g‖) at hu
  change (∀ x ∈ frontier U, Q.solution x=0) at hzero
  have hpexist := actual_continuous_domain_holder_jet_lift_four
    hU hK hproper hconv hrho hdia hR D.coeff.hlam D.coeff.Λ_pos halpha halpha1 hKa
    (by positivity : 0 ≤ (Kd+Bd)*‖g‖) (by positivity : 0 ≤ Bd*‖g‖)
    (by positivity : 0 ≤ ‖D.operator‖*‖g‖) hM hKb hball hdiam Q
    (fun x hx => hf x (subset_closure hx)) (fun x hx => hu x (subset_closure hx)) hzero J
  refine ⟨Classical.choose hpexist,(Classical.choose_spec hpexist).trans ?_⟩
  apply ContinuousMap.ext
  intro x
  exact actualClosureExtensionTwo_apply U _ x.property

theorem actual_holder_lifted_response_equation_two
    {U : Set E} [CompactSpace (closure U)]
    (hU : IsOpen U) (hK : IsCompact (closure U))
    {alpha Ka Kd Bd : ℝ} (halpha : 0 < alpha) (halpha1 : alpha < 1)
    (hKa : 0 ≤ Ka) (hKd : 0 ≤ Kd) (hBd : 0 ≤ Bd)
    (D : ActualHolderWeakResponseDataTwo U alpha Ka Kd Bd)
    (S : actualHolderLoadSpaceTwo (closure U) ℝ alpha →L[ℝ] actualHolderC2JetSpaceTwo U alpha)
    (hS : (actualHolderC2JetSpaceTwo_value U alpha).comp S=
      D.operator.comp (actualHolderLoadSpaceTwo_value (closure U) ℝ alpha))
    (g : actualHolderLoadSpaceTwo (closure U) ℝ alpha) :
    let u := actualClosureExtensionTwo U (actualHolderC2JetSpaceTwo_value U alpha (S g))
    let v := actualClosureExtensionTwo U (actualHolderLoadSpaceTwo_value _ _ alpha g)
    ActualScalarWeakEquationTwo D.coeff (fun x => -(D.weight x*v x)) u ∧
      ContDiffOn ℝ 2 u U ∧
      ∀ x ∈ U, (∑ i, ∑ j, D.coeff.a x i j*euclideanHessian u x i j)=D.weight x*v x := by
  have hvalue := congrArg (fun Q : actualHolderLoadSpaceTwo (closure U) ℝ alpha →L[ℝ] C(closure U,ℝ) => Q g) hS
  change actualHolderC2JetSpaceTwo_value U alpha (S g)=D.operator (actualHolderLoadSpaceTwo_value _ _ alpha g) at hvalue
  dsimp only
  rw [hvalue]
  exact actual_holder_weak_response_classical_two hU hK D.coeff D.positive D.regular D.divergence
    halpha halpha1 hKa hKd hBd D.holder D.weight_continuous D.weight_bound D.weight_holder
    D.operator D.weak g

end PowerConvexity
