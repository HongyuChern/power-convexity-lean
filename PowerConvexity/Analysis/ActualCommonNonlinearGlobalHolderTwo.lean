import PowerConvexity.Analysis.ActualNonlinearGlobalHolderFromBoundaryTwo
import PowerConvexity.Analysis.ActualCommonNonlinearClosureBoundaryModulusTwo

/-! # Whole-closure Hessian Holder control before all actual moving domains

The common actual geometry supplies the true boundary estimate. Combining
it with the radius-uniform nonlinear interior estimate gives one exponent
and one constant before the domain, defining function, density, solution
and actual closure jet.
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

theorem actual_common_nonlinear_global_holder_two
    {r Hchart F delta rho0 Dout G H P D Csrc : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hHchart : 0 < Hchart) (hdelta : 0 < delta)
    (hrho0 : 0 < rho0) (hDout : 0 ≤ Dout)
    (hG : 0 ≤ G) (hH : 0 ≤ H) (hP : 0 ≤ P) (hF : 0 ≤ F)
    (hD : 1 ≤ D) (hCsrc : 0 ≤ Csrc) :
    ∃ alpha : ℝ, 0 < alpha ∧ alpha < 1 ∧ ∃ K ≥ 0,
      ∀ Geo : ActualCommonNonlinearBoundaryGeometryFour r Hchart F delta rho0 Dout,
      ∀ u density : E → ℝ, ContDiffOn ℝ 4 u Geo.domain → ContDiffOn ℝ 2 density Geo.domain →
      ContinuousOn density (closure Geo.domain) → ∀ J : ClosureC2Jet u Geo.domain,
      (∀ x ∈ frontier Geo.domain, u x=0) →
      (∀ x ∈ Geo.domain, (complexHessian realDirections imagDirections u x).PosDef) →
      (∀ x ∈ Geo.domain, (complexHessian realDirections imagDirections u x).det=(density x : ℂ)) →
      (∀ x ∈ Geo.domain, 1 ≤ density x ∧ density x ≤ D) →
      (∀ x ∈ closure Geo.domain, ‖J.derivative x‖ ≤ G) →
      (∀ x ∈ closure Geo.domain, ‖J.hessian x‖ ≤ H) →
      (∀ x ∈ Geo.domain, ‖fderiv ℝ density x‖ ≤ P) →
      (∀ x ∈ Geo.domain, ∀ v : E,
        -(Csrc*‖v‖^2) ≤ (realHessian density x v v*density x-(fderiv ℝ density x v)^2)/(density x)^2) →
      ∀ x ∈ closure Geo.domain, ∀ y ∈ closure Geo.domain,
        ‖J.hessian x-J.hessian y‖ ≤ K*‖x-y‖^alpha := by
  obtain ⟨R,hR,hR1,gamma,hgamma,hgamma1,C,hC,hboundary⟩ :=
    actual_common_nonlinear_closure_boundary_hessian_modulus_two hr hr1 hHchart hdelta
      hrho0 hDout hG hH hP hF hD hCsrc
  obtain ⟨alpha,halpha,halpha1,K,hK,hglobal⟩ :=
    actual_nonlinear_global_holder_from_boundary_two hH hD hP hCsrc hR hgamma hC
  refine ⟨alpha,halpha,halpha1,K,hK,?_⟩
  intro Geo u density hu hrho hrhoC J hzero hpos hdet hrhob hJu hJH hrhoD hsource
  exact hglobal Geo.domain Geo.isOpen Geo.proper Geo.convex u density hu hrho J
    hpos hdet hrhob hJH hrhoD hsource
    (hboundary Geo u density hu hrho hrhoC J hzero hpos hdet hrhob hJu hJH hrhoD hsource)

end PowerConvexity
