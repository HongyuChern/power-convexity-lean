import PowerConvexity.Analysis.ActualCommonNonlinearBoundaryModulusTwo
import PowerConvexity.Analysis.ActualCommonBoundaryHessianCompatibilityTwo
import PowerConvexity.Analysis.ActualUniformBoundaryHessianModulusFour

/-! # True closure-Hessian boundary modulus uniform before all moving domains

The common nearest-boundary estimate and common boundary compatibility
cover every closure point and every nearby original boundary base point.
The domain and true defining function occur only after the constants.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3400000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_common_nonlinear_closure_boundary_hessian_modulus_two
    {r Hchart F delta rho0 Dout G H P D Csrc : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hHchart : 0 < Hchart) (hdelta : 0 < delta)
    (hrho0 : 0 < rho0) (hDout : 0 ≤ Dout)
    (hG : 0 ≤ G) (hH : 0 ≤ H) (hP : 0 ≤ P) (hF : 0 ≤ F)
    (hD : 1 ≤ D) (hCsrc : 0 ≤ Csrc) :
    ∃ R > 0, R ≤ 1 ∧ ∃ alpha : ℝ, 0 < alpha ∧ alpha < 1 ∧ ∃ C ≥ 0,
      ∀ Geo : ActualCommonNonlinearBoundaryGeometryFour r Hchart F delta rho0 Dout,
      ∀ u rho : E → ℝ, ContDiffOn ℝ 4 u Geo.domain → ContDiffOn ℝ 2 rho Geo.domain →
      ContinuousOn rho (closure Geo.domain) → ∀ J : ClosureC2Jet u Geo.domain,
      (∀ x ∈ frontier Geo.domain, u x=0) →
      (∀ x ∈ Geo.domain, (complexHessian realDirections imagDirections u x).PosDef) →
      (∀ x ∈ Geo.domain, (complexHessian realDirections imagDirections u x).det=(rho x : ℂ)) →
      (∀ x ∈ Geo.domain, 1 ≤ rho x ∧ rho x ≤ D) →
      (∀ x ∈ closure Geo.domain, ‖J.derivative x‖ ≤ G) →
      (∀ x ∈ closure Geo.domain, ‖J.hessian x‖ ≤ H) →
      (∀ x ∈ Geo.domain, ‖fderiv ℝ rho x‖ ≤ P) →
      (∀ x ∈ Geo.domain, ∀ v : E,
        -(Csrc*‖v‖^2) ≤ (realHessian rho x v v*rho x-(fderiv ℝ rho x v)^2)/(rho x)^2) →
      ∀ c ∈ frontier Geo.domain, ∀ x ∈ closure Geo.domain, ‖x-c‖ < R →
        ‖J.hessian x-J.hessian c‖ ≤ C*‖x-c‖^alpha := by
  obtain ⟨Rn,hRn,hRn1,gamma,hgamma,hgamma1,Cn,hCn,hnear⟩ :=
    actual_common_nonlinear_nearest_boundary_hessian_modulus_two
      (rho0 := rho0) (Dout := Dout) hr hr1 hHchart hdelta hG hH hP hF hD hCsrc
  obtain ⟨Rb,hRb,hRb1,beta,hbeta,hbeta1,Cb,hCb,hboundary⟩ :=
    actual_common_boundary_hessian_compatibility_two hr hr1 hHchart hdelta hrho0 hDout
      hG hH hP hF
  let alpha := min gamma beta
  have halpha : 0 < alpha := lt_min hgamma hbeta
  have halpha1 : alpha < 1 := (min_le_left _ _).trans_lt hgamma1
  let R := min Rn (Rb/2)
  have hR : 0 < R := lt_min hRn (half_pos hRb)
  let C := Cn+Cb*(2 : ℝ)^alpha
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨R,hR,(min_le_left _ _).trans hRn1,alpha,halpha,halpha1,C,hC,?_⟩
  intro Geo u rho hu hrho hrhoC J hzero hpos hdet hrhob hJu hJH hrhoD hsource c hc x hx hxc
  let U := Geo.domain
  let g := Geo.defining
  have hU : IsOpen U := Geo.isOpen
  have hconv : Convex ℝ U := Geo.convex
  have hproper : U≠univ := Geo.proper
  have hg : ContDiff ℝ 3 g := Geo.regular
  have hgb := Geo.boundary
  have hgdef := Geo.side
  have hg1 := Geo.firstBound
  have hg2 := Geo.secondBound
  have hg3 := Geo.thirdBound
  have hnear' : ∀ z ∈ U, infDist z (frontier U) < Rn →
      ‖realHessian u z-J.hessian (actualBoundaryFootOnDomainFour U hproper z)‖ ≤
        Cn*(infDist z (frontier U))^alpha := by
    intro z hz hzR
    exact (hnear Geo u rho hu hrho hrhoC J hzero hpos hdet hrhob hJu hJH hrhoD hsource z hz hzR).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge' infDist_nonneg
        (hzR.le.trans hRn1) halpha.le (min_le_left _ _)) hCn)
  have hboundary' : ∀ a ∈ frontier U, ∀ b ∈ frontier U, ‖a-b‖ < Rb →
      ‖J.hessian a-J.hessian b‖ ≤ Cb*‖a-b‖^alpha := by
    intro a ha b hb hab
    exact (hboundary Geo u rho hu (hrho.of_le (by norm_num)) hrhoC J hzero hpos hdet
      (fun z hz => (hrhob z hz).1) hJu hJH hrhoD a ha b hb hab).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge' (norm_nonneg _)
        (hab.le.trans hRb1) halpha.le (min_le_right _ _)) hCb)
  have hh := actual_domain_extension_boundary_holder_four
    (Z := E →L[ℝ] E →L[ℝ] ℝ) (f := realHessian u) (g := J.hessian) hU hproper hCn hCb halpha.le
    hnear' hboundary' hc hx hxc
  have hsame : actualDomainJetExtensionFour U (realHessian u) J.hessian x=J.hessian x := by
    by_cases hxi : x ∈ U
    · rw [actualDomainJetExtensionFour,if_pos hxi,J.hessian_eq hxi]
      rfl
    · rw [actualDomainJetExtensionFour,if_neg hxi]
  rw [hsame] at hh
  exact hh


end PowerConvexity
