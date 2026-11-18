import PowerConvexity.Analysis.ActualUniformNonlinearBoundaryModulusTwo
import PowerConvexity.Analysis.ActualUniformBoundaryHessianCompatibilityTwo
import PowerConvexity.Analysis.ActualUniformBoundaryHessianModulusFour

/-! # A common true closure-Hessian modulus at every original boundary point

The actual nearest-boundary decay and same-family boundary compatibility
are combined with their correct exponents. The conclusion covers every
closure point and every nearby true boundary base point of the original
domain. No unknown boundary modulus is an input.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_uniform_nonlinear_closure_boundary_hessian_modulus_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hne : U.Nonempty) (hproper : U≠univ) {g : E → ℝ} (hg : ContDiff ℝ 3 g)
    (hgb : ∀ c ∈ frontier U, g c=0 ∧ fderiv ℝ g c≠0)
    (hgdef : ∀ c ∈ frontier U, ∀ᶠ z in 𝓝 c, z∈U ↔ g z<0)
    {G H P F D Csrc : ℝ} (hG : 0 ≤ G) (hH : 0 ≤ H) (hP : 0 ≤ P)
    (hF : 0 ≤ F) (hD : 1 ≤ D) (hCsrc : 0 ≤ Csrc)
    (hg1 : ∀ x ∈ closure U, ‖fderiv ℝ g x‖ ≤ F)
    (hg2 : ∀ x ∈ closure U, ‖realHessian g x‖ ≤ F)
    (hg3 : ∀ x ∈ closure U, ‖fderiv ℝ (realHessian g) x‖ ≤ F) :
    ∃ R > 0, R ≤ 1 ∧ ∃ alpha : ℝ, 0 < alpha ∧ alpha < 1 ∧ ∃ C ≥ 0,
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
      ∀ c ∈ frontier U, ∀ x ∈ closure U, ‖x-c‖ < R →
        ‖J.hessian x-J.hessian c‖ ≤ C*‖x-c‖^alpha := by
  obtain ⟨Rn,hRn,hRn1,gamma,hgamma,hgamma1,Cn,hCn,hnear⟩ :=
    actual_uniform_nonlinear_nearest_boundary_hessian_modulus_two hU hconv hK hproper hg hgb hgdef
      hG hH hP hF hD hCsrc hg1 hg2 hg3
  obtain ⟨Rb,hRb,hRb1,beta,hbeta,hbeta1,Cb,hCb,hboundary⟩ :=
    actual_uniform_boundary_hessian_compatibility_two hU hconv hK hne hg hgb hgdef
      hG hH hP hF hg1 hg2 hg3
  let alpha := min gamma beta
  have halpha : 0 < alpha := lt_min hgamma hbeta
  have halpha1 : alpha < 1 := (min_le_left _ _).trans_lt hgamma1
  let R := min Rn (Rb/2)
  have hR : 0 < R := lt_min hRn (half_pos hRb)
  let C := Cn+Cb*(2 : ℝ)^alpha
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨R,hR,(min_le_left _ _).trans hRn1,alpha,halpha,halpha1,C,hC,?_⟩
  intro u rho hu hrho hrhoC J hzero hpos hdet hrhob hJu hJH hrhoD hsource c hc x hx hxc
  have hnear' : ∀ z ∈ U, infDist z (frontier U) < Rn →
      ‖realHessian u z-J.hessian (actualBoundaryFootOnDomainFour U hproper z)‖ ≤
        Cn*(infDist z (frontier U))^alpha := by
    intro z hz hzR
    exact (hnear u rho hu hrho hrhoC J hzero hpos hdet hrhob hJu hJH hrhoD hsource z hz hzR).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge' infDist_nonneg
        (hzR.le.trans hRn1) halpha.le (min_le_left _ _)) hCn)
  have hboundary' : ∀ a ∈ frontier U, ∀ b ∈ frontier U, ‖a-b‖ < Rb →
      ‖J.hessian a-J.hessian b‖ ≤ Cb*‖a-b‖^alpha := by
    intro a ha b hb hab
    exact (hboundary u rho hu (hrho.of_le (by norm_num)) hrhoC J hzero hpos hdet
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
