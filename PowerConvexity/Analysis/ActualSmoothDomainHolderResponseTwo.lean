import PowerConvexity.Analysis.ActualHolderResponseFromBoundaryTwo
import PowerConvexity.Analysis.ActualUniformDomainBoundaryExpansionFour

/-! # A genuine bounded Holder response on the actual smooth convex domain

The boundary expansions are now proved from the actual defining function,
the original coefficients, the continuous weighted load, and the true zero
boundary of the same complete C0 response. No boundary expansion or Schauder
estimate is an input to this theorem. Closed graph provides the bounded
operator between the complete actual Holder load and zero-boundary C2 jet
spaces.
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

theorem actual_smooth_domain_bounded_holder_response_two
    {U : Set E} [CompactSpace (closure U)]
    (hU : IsOpen U) (hK : IsCompact (closure U)) (hproper : U ≠ univ) (hconv : Convex ℝ U)
    {o : E} {rho diameter alpha Ka Kd Bd : ℝ}
    (hrho : 0 < rho) (hdia : 0 ≤ diameter)
    (hball : closedBall o rho ⊆ U) (hdiam : ∀ c ∈ frontier U, ‖o-c‖ ≤ diameter)
    {phi : E → ℝ} (hphi : ContDiff ℝ 3 phi)
    (hphi0 : ∀ c ∈ frontier U, phi c=0) (hDphi : ∀ c ∈ frontier U, fderiv ℝ phi c ≠ 0)
    (hdef : ∀ c ∈ frontier U, ∀ᶠ z in 𝓝 c, z ∈ U ↔ phi z < 0)
    (halpha : 0 < alpha) (halpha1 : alpha < 1)
    (hKa : 0 ≤ Ka) (hKd : 0 ≤ Kd) (hBd : 0 ≤ Bd)
    (D : ActualHolderWeakResponseDataTwo U alpha Ka Kd Bd) :
    ∃! S : actualHolderLoadSpaceTwo (closure U) ℝ alpha →L[ℝ] actualHolderC2JetSpaceTwo U alpha,
      (actualHolderC2JetSpaceTwo_value U alpha).comp S=
        D.operator.comp (actualHolderLoadSpaceTwo_value (closure U) ℝ alpha) := by
  apply actual_holder_response_from_boundary_expansion_two hU hK hproper hconv hrho hdia
    hball hdiam halpha halpha1 hKa hKd hBd D
  intro g
  let Q := D.domainData hU hK halpha halpha1 hKa hKd hBd g
  have hb := D.domainData_bounds hU hK halpha halpha1 hKa hKd hBd g
  have hex := actual_uniform_continuous_domain_boundary_expansion_four
    hU hK hphi hphi0 hDphi hdef D.coeff.hlam D.coeff.Λ_pos halpha halpha1 hKa
    (by positivity : 0 ≤ (Kd+Bd)*‖g‖)
    (by positivity : 0 ≤ ‖D.operator‖*‖g‖) (by positivity : 0 ≤ Bd*‖g‖)
  let R : ℝ := Classical.choose hex
  have hR : 0 < R := (Classical.choose_spec hex).1
  have hmex := (Classical.choose_spec hex).2
  let M : ℝ := Classical.choose hmex
  have hM : 0 ≤ M := (Classical.choose_spec hmex).1
  have htex := (Classical.choose_spec hmex).2
  let T : ℝ := Classical.choose htex
  have hT : 0 ≤ T := (Classical.choose_spec htex).1
  have hgex := (Classical.choose_spec htex).2
  have hglobal := (Classical.choose_spec hgex).2
  have hj := hglobal Q hb.2.2 hb.2.1 hb.1
  exact ⟨R,hR,M,hM,T,hT,⟨Classical.choose hj⟩⟩

end PowerConvexity
