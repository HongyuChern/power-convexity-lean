import PowerConvexity.Analysis.ActualUniformRoughDomainDataFour
import PowerConvexity.Analysis.VariableDensityCofactorEllipticity
import PowerConvexity.Analysis.ActualUniformGraphDriftBoundsFour

/-! # Common rough Dirichlet data from the same actual nonlinear solutions

The normalizing scalar, ellipticity and source bound precede every nonlinear
solution. The coefficient is its actual cofactor and the response is its real
closure derivative in a defining tangential field. There is no input modulus
for the solution Hessian or coefficient.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_uniform_cofactor_dirichlet_data_four
    {G H P F : ℝ} (hG : 0 ≤ G) (hH : 0 ≤ H) (hP : 0 ≤ P) (hF : 0 ≤ F) :
    ∃ c > 0, ∃ Lambda ≥ 1, ∃ S ≥ 0,
      ∀ U : Set E, ∀ hU : IsOpen U, Convex ℝ U →
      ∀ u rho g : E → ℝ, ContDiffOn ℝ 4 u U → ContDiffOn ℝ 1 rho U → ContDiff ℝ 3 g →
      ∀ J : ClosureC2Jet u U,
      (∀ x ∈ frontier U, u x=0) →
      (∀ x ∈ frontier U, g x=0 ∧ fderiv ℝ g x≠0) →
      (∀ x ∈ frontier U, ∀ᶠ z in 𝓝 x, z∈U ↔ g z<0) →
      (∀ x ∈ U, (complexHessian realDirections imagDirections u x).PosDef) →
      (∀ x ∈ U, (complexHessian realDirections imagDirections u x).det=(rho x : ℂ)) →
      (∀ x ∈ U, 1 ≤ rho x) →
      (∀ x ∈ closure U, ‖J.derivative x‖ ≤ G) →
      (∀ x ∈ U, ‖realHessian u x‖ ≤ H) →
      (∀ x ∈ U, ‖fderiv ℝ rho x‖ ≤ P) →
      (∀ x ∈ closure U, ‖fderiv ℝ g x‖ ≤ F) →
      (∀ x ∈ closure U, ‖realHessian g x‖ ≤ F) →
      (∀ x ∈ closure U, ‖fderiv ℝ (realHessian g) x‖ ≤ F) →
      ∀ e N : E, ‖e‖=1 → ‖N‖=1 →
      ∃ D : ActualRoughDomainDirichletDataFour U 1 Lambda S (G*(2*F)),
        (∀ x ∈ U, D.coeff.a x=c⁻¹ • complexCofactorCoeff u x) ∧
        D.solution=actualClosureTangentialResponseFour J (actualDefiningTangentialFieldFour g e N) ∧
        D.source=actualTangentialCofactorLoadFour c u rho
          (actualDefiningTangentialFieldFour g e N) D.coeff.a := by
  obtain ⟨c,hc,Lambda,hLambda,hcoeff⟩ := exists_uniform_variable_density_cofactor_coefficients (n := 2) H
  let S := c⁻¹*P*(2*F)+16*Lambda*(2*H*(2*F)+G*(2*F))
  refine ⟨c,hc,Lambda,hLambda,S,by dsimp [S]; positivity,?_⟩
  intro U hU hconv u rho g hu hrho hg J hzero hgb hgdef hpos hdet hrho1 hJu huH hrhoD hg1 hg2 hg3 e N he hN
  have hdet1 : ∀ x ∈ U, 1 ≤ (complexHessian realDirections imagDirections u x).det.re := by
    intro x hx
    rw [hdet x hx,Complex.ofReal_re]
    exact hrho1 x hx
  have hentry : ∀ x ∈ U, ∀ i j, |euclideanHessian u x i j| ≤ H := by
    intro x hx i j
    exact (actual_bilinear_coordinate_bound_four (realHessian u x) i j).trans (huH x hx)
  obtain ⟨A,hAL,hA⟩ := hcoeff U hU u hu hdet1 hpos hentry
  obtain ⟨hreg,hdiv⟩ := actual_scaled_cofactor_C1_divergence_two hU hu hpos hA
  obtain ⟨hv,hvC,hvz,hvb,hfC,hfb,heq⟩ :=
    actual_defining_tangential_dirichlet_response_four hU hconv hu hrho hg J hzero hgb hgdef
      hpos hdet hc hG hH hP hF A.1 hA hJu huH hrhoD hg1 hg2 hg3 he hN
  let D : ActualRoughDomainDirichletDataFour U 1 Lambda S (G*(2*F)) := {
    coeff := A.1
    source := actualTangentialCofactorLoadFour c u rho (actualDefiningTangentialFieldFour g e N) A.1.a
    solution := actualClosureTangentialResponseFour J (actualDefiningTangentialFieldFour g e N)
    lower := by rw [A.property]
    upper := hAL.le
    positive := by
      intro x hx
      rw [hA x hx]
      exact (complexCofactorCoeff_posDef (hpos x hx)).smul (inv_pos.mpr hc)
    regular := hreg
    divergence := hdiv
    source_continuous := hfC
    source_bound := by
      intro x hx
      simpa only [hAL,S] using hfb x hx
    solution_regular := hv
    solution_continuous := hvC
    solution_zero := hvz
    solution_bound := hvb
    equation := heq
  }
  exact ⟨D,hA,rfl,rfl⟩

end PowerConvexity
