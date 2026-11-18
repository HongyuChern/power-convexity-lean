import PowerConvexity.Analysis.ActualCommonChartRoughBoundaryExpansionFour
import PowerConvexity.Analysis.ActualUniformTangentialBoundaryExpansionFour

/-! # Genuine common geometry for moving nonlinear Dirichlet domains

All numerical geometry is fixed before the domain and its true defining
function. The record contains actual physical charts and actual fixed-ball
geometry, with no derivative modulus of an unknown solution.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

structure ActualCommonNonlinearBoundaryGeometryFour (r Hchart F delta rho D : ℝ) where
  domain : Set E
  defining : E → ℝ
  isOpen : IsOpen domain
  convex : Convex ℝ domain
  compactClosure : IsCompact (closure domain)
  charts : ActualUnitBoundaryChartsFour domain r Hchart
  regular : ContDiff ℝ 3 defining
  boundary : ∀ c ∈ frontier domain, defining c=0 ∧ fderiv ℝ defining c≠0
  side : ∀ c ∈ frontier domain, ∀ᶠ z in 𝓝 c, z∈domain ↔ defining z<0
  firstBound : ∀ x ∈ closure domain, ‖fderiv ℝ defining x‖ ≤ F
  secondBound : ∀ x ∈ closure domain, ‖realHessian defining x‖ ≤ F
  thirdBound : ∀ x ∈ closure domain, ‖fderiv ℝ (realHessian defining) x‖ ≤ F
  normalMargin : ∀ c ∈ frontier domain, delta ≤ ‖fderiv ℝ defining c‖
  center : E
  innerBall : closedBall center rho ⊆ domain
  boundaryRadius : ∀ c ∈ frontier domain, ‖center-c‖ ≤ D

theorem ActualCommonNonlinearBoundaryGeometryFour.proper
    {r Hchart F delta rho D : ℝ}
    (Geo : ActualCommonNonlinearBoundaryGeometryFour r Hchart F delta rho D) :
    Geo.domain≠univ := by
  intro h
  apply Geo.compactClosure.ne_univ
  rw [h,closure_univ]

theorem actual_common_geometry_tangential_boundary_expansion_four
    {r Hchart F delta rho0 D G H P : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hHchart : 0 < Hchart)
    (hG : 0 ≤ G) (hH : 0 ≤ H) (hP : 0 ≤ P) (hF : 0 ≤ F) :
    ∃ R > 0, ∃ alpha : ℝ, 0 < alpha ∧ alpha < 1 ∧ ∃ C ≥ 0, ∃ Q ≥ 0,
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
      ∀ e N : E, ‖e‖=1 → ‖N‖=1 → ∀ c ∈ frontier Geo.domain,
      let T := actualDefiningTangentialFieldFour Geo.defining e N
      ‖actualClosureTangentialDerivativeFour J T c‖ ≤ Q ∧
      ∀ x ∈ Geo.domain, ‖x-c‖ < R →
        |actualClosureTangentialResponseFour J T x-
          actualClosureTangentialDerivativeFour J T c (x-c)| ≤ C*‖x-c‖*‖x-c‖^alpha := by
  obtain ⟨s,hs,Lambda,hLambda,S,hS,hdata⟩ := actual_uniform_cofactor_dirichlet_data_four hG hH hP hF
  obtain ⟨R,hR,alpha,ha,ha1,C,hC,Q,hQ,hexp⟩ :=
    actual_common_chart_rough_boundary_expansion_four hr hr1 hHchart
      (by norm_num : (0 : ℝ) < 1) hLambda hS (show 0 ≤ G*(2*F) by positivity)
  refine ⟨R,hR,alpha,ha,ha1,C,hC,Q,hQ,?_⟩
  intro Geo u density hu hrho J hzero hpos hdet hrho1 hJu huH hrhoD e N he hN c hc
  let T := actualDefiningTangentialFieldFour Geo.defining e N
  obtain ⟨Da,_,hsol,_⟩ := hdata Geo.domain Geo.isOpen Geo.convex u density Geo.defining hu hrho
    Geo.regular J hzero Geo.boundary Geo.side hpos hdet hrho1 hJu huH hrhoD
    Geo.firstBound Geo.secondBound Geo.thirdBound e N he hN
  obtain ⟨L,hL,herr⟩ := hexp Geo.domain Geo.isOpen Geo.charts Da c hc
  have hv0 : actualClosureTangentialResponseFour J T c=0 := by
    rw [←hsol]
    exact Da.solution_zero c hc
  have hvErr : ∀ x ∈ Geo.domain, ‖x-c‖ < R →
      |actualClosureTangentialResponseFour J T x-L (x-c)| ≤ C*‖x-c‖*‖x-c‖^alpha := by
    simpa only [hsol] using herr
  have hT : ContDiff ℝ 2 T := contDiffOn_univ.mp
    (actual_defining_tangential_field_regular_four isOpen_univ Geo.regular.contDiffOn e N)
  have hJD := actual_closure_tangential_response_hasFDerivWithinAt_four Geo.isOpen Geo.convex
    (hu.of_le (by norm_num)) J (frontier_subset_closure hc)
    ((hT.contDiffAt (x := c)).differentiableAt (by norm_num))
  have hid : actualClosureTangentialDerivativeFour J T c=L :=
    actual_affine_remainder_identifies_closure_derivative_four Geo.isOpen Geo.convex
      (frontier_subset_closure hc) hR hC ha hv0 hJD hvErr
  change ‖actualClosureTangentialDerivativeFour J T c‖ ≤ Q ∧ _
  rw [hid]
  exact ⟨hL,hvErr⟩

end PowerConvexity
