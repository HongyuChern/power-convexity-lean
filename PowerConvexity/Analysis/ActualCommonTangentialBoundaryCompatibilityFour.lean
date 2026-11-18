import PowerConvexity.Analysis.ActualCommonNonlinearBoundaryGeometryFour
import PowerConvexity.Analysis.ActualConvexBoundaryLinearJetComparisonFour

/-! # Uniform boundary compatibility from common physical and interior geometry

One genuine interior probe ball and one outer boundary radius determine
constants before all domains. The response is the same global defining
tangent field at both boundary points of each actual domain.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_common_tangential_boundary_compatibility_four
    {r Hchart F delta rho0 D G H P : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hHchart : 0 < Hchart)
    (hrho0 : 0 < rho0) (hD : 0 ≤ D)
    (hG : 0 ≤ G) (hH : 0 ≤ H) (hP : 0 ≤ P) (hF : 0 ≤ F) :
    ∃ R > 0, R ≤ 1 ∧ ∃ alpha : ℝ, 0 < alpha ∧ alpha < 1 ∧ ∃ C ≥ 0,
      ∀ Geo : ActualCommonNonlinearBoundaryGeometryFour r Hchart F delta rho0 D,
      ∀ u density : E → ℝ, ContDiffOn ℝ 4 u Geo.domain → ContDiffOn ℝ 1 density Geo.domain →
      ∀ J : ClosureC2Jet u Geo.domain,
      (∀ x ∈ frontier Geo.domain, u x=0) →
      (∀ x ∈ Geo.domain, (complexHessian realDirections imagDirections u x).PosDef) →
      (∀ x ∈ Geo.domain, (complexHessian realDirections imagDirections u x).det=(density x : ℂ)) →
      (∀ x ∈ Geo.domain, 1 ≤ density x) →
      (∀ x ∈ closure Geo.domain, ‖J.derivative x‖ ≤ G) →
      (∀ x ∈ Geo.domain, ‖realHessian u x‖ ≤ H) →
      (∀ x ∈ Geo.domain, ‖fderiv ℝ density x‖ ≤ P) →
      ∀ e N : E, ‖e‖=1 → ‖N‖=1 →
      ∀ c ∈ frontier Geo.domain, ∀ d ∈ frontier Geo.domain, ‖c-d‖ < R →
      let T := actualDefiningTangentialFieldFour Geo.defining e N
      ‖actualClosureTangentialDerivativeFour J T c-
        actualClosureTangentialDerivativeFour J T d‖ ≤ C*‖c-d‖^alpha := by
  obtain ⟨R,hR,alpha,ha,ha1,C,hC,Q,hQ,hexp⟩ :=
    actual_common_geometry_tangential_boundary_expansion_four
      (delta := delta) (rho0 := rho0) (D := D) hr hr1 hHchart hG hH hP hF
  let radius := min 1 (min (R/4) (D+rho0))
  have hradius : 0 < radius := lt_min zero_lt_one (lt_min (by positivity) (by positivity))
  let K := 72*C*(4 : ℝ)^alpha*(D+rho0)^2/rho0^2
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨radius,hradius,min_le_left _ _,alpha,ha,ha1,K,hK,?_⟩
  intro Geo u density hu hrho J hzero hpos hdet hrho1 hJu huH hrhoD e N he hN c hc d hd hnear
  let T := actualDefiningTangentialFieldFour Geo.defining e N
  have herr : ∀ a ∈ frontier Geo.domain, ∀ x ∈ Geo.domain, ‖x-a‖ < R →
      |actualClosureTangentialResponseFour J T x-
        actualClosureTangentialDerivativeFour J T a (x-a)| ≤ C*‖x-a‖*‖x-a‖^alpha := by
    intro a ha
    exact (hexp Geo u density hu hrho J hzero hpos hdet hrho1 hJu huH hrhoD e N he hN a ha).2
  exact actual_convex_boundary_linear_derivative_holder_four Geo.isOpen Geo.convex hrho0 hD hR hC
    ha.le Geo.innerBall frontier_subset_closure Geo.boundaryRadius herr c hc d hd
    (hnear.trans_le (min_le_right _ _))

end PowerConvexity
