import PowerConvexity.Analysis.ActualNonlinearGlobalHolderFromBoundaryTwo
import PowerConvexity.Analysis.ActualUniformNonlinearClosureBoundaryModulusTwo

/-! # Actual whole-closure Hessian Holder estimates for the common nonlinear family

The true boundary modulus is now discharged by the actual tangential
response argument. No coefficient Holder assumption, third-derivative bound
or supplied boundary modulus occurs in this common-data estimate.
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

theorem actual_uniform_nonlinear_global_holder_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hne : U.Nonempty) (hproper : U≠univ) {g : E → ℝ} (hg : ContDiff ℝ 3 g)
    (hgb : ∀ c ∈ frontier U, g c=0 ∧ fderiv ℝ g c≠0)
    (hgdef : ∀ c ∈ frontier U, ∀ᶠ z in 𝓝 c, z∈U ↔ g z<0)
    {G H P F D Csrc : ℝ} (hG : 0 ≤ G) (hH : 0 ≤ H) (hP : 0 ≤ P)
    (hF : 0 ≤ F) (hD : 1 ≤ D) (hCsrc : 0 ≤ Csrc)
    (hg1 : ∀ x ∈ closure U, ‖fderiv ℝ g x‖ ≤ F)
    (hg2 : ∀ x ∈ closure U, ‖realHessian g x‖ ≤ F)
    (hg3 : ∀ x ∈ closure U, ‖fderiv ℝ (realHessian g) x‖ ≤ F) :
    ∃ alpha : ℝ, 0 < alpha ∧ alpha < 1 ∧ ∃ K ≥ 0,
      ∀ u rho : E → ℝ, ContDiffOn ℝ 4 u U → ContDiffOn ℝ 2 rho U →
      ContinuousOn rho (closure U) → ∀ J : ClosureC2Jet u U,
      (∀ x ∈ frontier U, u x=0) →
      (∀ x ∈ U, (complexHessian realDirections imagDirections u x).PosDef) →
      (∀ x ∈ U, (complexHessian realDirections imagDirections u x).det=(rho x : ℂ)) →
      (∀ x ∈ U, 1 ≤ rho x ∧ rho x ≤ D) →
      (∀ x ∈ closure U, ‖J.derivative x‖ ≤ G) →
      (∀ x ∈ closure U, ‖J.hessian x‖ ≤ H) →
      (∀ x ∈ U, ‖fderiv ℝ rho x‖ ≤ P) →
      (∀ x ∈ U, ∀ v : E,
        -(Csrc*‖v‖^2) ≤ (realHessian rho x v v*rho x-(fderiv ℝ rho x v)^2)/(rho x)^2) →
      ∀ x ∈ closure U, ∀ y ∈ closure U,
        ‖J.hessian x-J.hessian y‖ ≤ K*‖x-y‖^alpha := by
  obtain ⟨R,hR,hR1,gamma,hgamma,hgamma1,C,hC,hboundary⟩ :=
    actual_uniform_nonlinear_closure_boundary_hessian_modulus_two hU hconv hK hne hproper
      hg hgb hgdef hG hH hP hF hD hCsrc hg1 hg2 hg3
  obtain ⟨alpha,halpha,halpha1,K,hK0,hglobal⟩ :=
    actual_nonlinear_global_holder_from_boundary_two hH hD hP hCsrc hR hgamma hC
  refine ⟨alpha,halpha,halpha1,K,hK0,?_⟩
  intro u rho hu hrho hrhoC J hzero hpos hdet hrhob hJu hJH hrhoD hsource
  exact hglobal U hU hproper hconv u rho hu hrho J hpos hdet hrhob hJH hrhoD hsource
    (hboundary u rho hu hrho hrhoC J hzero hpos hdet hrhob hJu hJH hrhoD hsource)

end PowerConvexity
