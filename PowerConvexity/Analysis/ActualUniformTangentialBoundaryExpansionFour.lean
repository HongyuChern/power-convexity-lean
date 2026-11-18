import PowerConvexity.Analysis.ActualUniformCofactorDirichletDataFour
import PowerConvexity.Analysis.ActualUniformRoughBoundaryExpansionFour
import PowerConvexity.Analysis.ActualUniformFirstBoundaryDerivativeFour

/-! # The actual nonlinear tangential response has a common boundary expansion

The same actual nonlinear solution supplies the cofactor equation, bounded
commutator and true zero trace. The rough quotient and genuine physical
charts give a common expansion. Uniqueness of the derivative on the original
convex domain identifies its covector with the actual closure jet.
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

theorem actual_uniform_tangential_boundary_expansion_four
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    {g : E → ℝ} (hg : ContDiff ℝ 3 g)
    (hgb : ∀ c ∈ frontier U, g c=0 ∧ fderiv ℝ g c≠0)
    (hgdef : ∀ c ∈ frontier U, ∀ᶠ z in 𝓝 c, z∈U ↔ g z<0)
    {G H P F : ℝ} (hG : 0 ≤ G) (hH : 0 ≤ H) (hP : 0 ≤ P) (hF : 0 ≤ F)
    (hg1 : ∀ x ∈ closure U, ‖fderiv ℝ g x‖ ≤ F)
    (hg2 : ∀ x ∈ closure U, ‖realHessian g x‖ ≤ F)
    (hg3 : ∀ x ∈ closure U, ‖fderiv ℝ (realHessian g) x‖ ≤ F) :
    ∃ R > 0, ∃ alpha : ℝ, 0 < alpha ∧ alpha < 1 ∧ ∃ C ≥ 0, ∃ Q ≥ 0,
      ∀ u rho : E → ℝ, ContDiffOn ℝ 4 u U → ContDiffOn ℝ 1 rho U →
      ∀ J : ClosureC2Jet u U,
      (∀ x ∈ frontier U, u x=0) →
      (∀ x ∈ U, (complexHessian realDirections imagDirections u x).PosDef) →
      (∀ x ∈ U, (complexHessian realDirections imagDirections u x).det=(rho x : ℂ)) →
      (∀ x ∈ U, 1 ≤ rho x) →
      (∀ x ∈ closure U, ‖J.derivative x‖ ≤ G) →
      (∀ x ∈ U, ‖realHessian u x‖ ≤ H) →
      (∀ x ∈ U, ‖fderiv ℝ rho x‖ ≤ P) →
      ∀ e N : E, ‖e‖=1 → ‖N‖=1 → ∀ c ∈ frontier U,
      let T := actualDefiningTangentialFieldFour g e N
      ‖actualClosureTangentialDerivativeFour J T c‖ ≤ Q ∧
      ∀ x ∈ U, ‖x-c‖ < R →
        |actualClosureTangentialResponseFour J T x-
          actualClosureTangentialDerivativeFour J T c (x-c)| ≤ C*‖x-c‖*‖x-c‖^alpha := by
  obtain ⟨s,hs,Lambda,hLambda,S,hS,hdata⟩ :=
    actual_uniform_cofactor_dirichlet_data_four hG hH hP hF
  obtain ⟨R,hR,alpha,ha,ha1,C,hC,Q,hQ,hexp⟩ :=
    actual_uniform_rough_domain_boundary_expansion_four hU hK hg
      (fun c hc => (hgb c hc).1) (fun c hc => (hgb c hc).2) hgdef
      (by norm_num : (0 : ℝ) < 1) hLambda hS (show 0 ≤ G*(2*F) by positivity)
  refine ⟨R,hR,alpha,ha,ha1,C,hC,Q,hQ,?_⟩
  intro u rho hu hrho J hzero hpos hdet hrho1 hJu huH hrhoD e N he hN c hc
  let T := actualDefiningTangentialFieldFour g e N
  obtain ⟨D,_,hsol,_⟩ := hdata U hU hconv u rho g hu hrho hg J hzero hgb hgdef
    hpos hdet hrho1 hJu huH hrhoD hg1 hg2 hg3 e N he hN
  obtain ⟨L,hL,herr⟩ := hexp D c hc
  have hv0 : actualClosureTangentialResponseFour J T c=0 := by
    rw [← hsol]
    exact D.solution_zero c hc
  have hvErr : ∀ x ∈ U, ‖x-c‖ < R →
      |actualClosureTangentialResponseFour J T x-L (x-c)| ≤ C*‖x-c‖*‖x-c‖^alpha := by
    simpa only [hsol] using herr
  have hT : ContDiff ℝ 2 T := contDiffOn_univ.mp
    (actual_defining_tangential_field_regular_four isOpen_univ hg.contDiffOn e N)
  have hJD := actual_closure_tangential_response_hasFDerivWithinAt_four hU hconv
    (hu.of_le (by norm_num)) J (frontier_subset_closure hc)
    ((hT.contDiffAt (x := c)).differentiableAt (by norm_num))
  have hid : actualClosureTangentialDerivativeFour J T c=L :=
    actual_affine_remainder_identifies_closure_derivative_four hU hconv
      (frontier_subset_closure hc) hR hC ha hv0 hJD hvErr
  change ‖actualClosureTangentialDerivativeFour J T c‖ ≤ Q ∧ _
  rw [hid]
  exact ⟨hL,hvErr⟩

end PowerConvexity
