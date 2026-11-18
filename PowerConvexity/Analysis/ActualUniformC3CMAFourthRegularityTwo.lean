import PowerConvexity.Analysis.ActualUniformC3FourthUpgradeTwo
import PowerConvexity.Analysis.ActualC3CofactorWeakVariationTwo

/-! # Genuine nonlinear C3 to C4 interior regularity

The real C3 weak second-variation theorem supplies the full weak equation.
The only Holder input is the actual third derivative, and the same actual
potential acquires C4 regularity and a quantitative fourth-jet modulus.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators ComplexOrder Matrix.Norms.Elementwise
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul
attribute [local instance] ahdTripleNormedGroup ahdTripleNormedSpace ahdTripleModule ahdTripleTopology

theorem actual_uniform_C3_CMA_fourth_regularity_two
    {r c lam Lambda H M K D₂ D₃ alpha : ℝ}
    (hr : 0 < r) (hc : 0 < c) (hlam : 0 < lam) (hLambda : 0 < Lambda)
    (hH : 0 ≤ H) (hM : 0 ≤ M) (hK : 0 ≤ K) (hD₂ : 0 ≤ D₂) (hD₃ : 0 ≤ D₃)
    (halpha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ delta > 0, delta ≤ r/4 ∧ ∃ Q ≥ 0,
      ∀ x₀ : E, ∀ U : Set E, IsOpen U → ∀ hclosed : closedBall x₀ (2*r) ⊆ U,
      ∀ u rho : E → ℝ, ContDiffOn ℝ 3 u U → ContDiffOn ℝ 3 rho U →
      (∀ x ∈ U, (complexHessian realDirections imagDirections u x).PosDef) →
      (∀ x ∈ U, (complexHessian realDirections imagDirections u x).det=(rho x : ℂ)) →
      (∀ x ∈ U, ‖realHessian u x‖ ≤ H) →
      (∀ x ∈ U, ‖fderiv ℝ (realHessian u) x‖ ≤ M) →
      (∀ x ∈ ball x₀ (2*r), ∀ y ∈ ball x₀ (2*r),
        ‖fderiv ℝ (realHessian u) x-fderiv ℝ (realHessian u) y‖ ≤ K*‖x-y‖^alpha) →
      (∀ x ∈ U, ‖realHessian rho x‖ ≤ D₂) →
      (∀ x ∈ U, ‖fderiv ℝ (realHessian rho) x‖ ≤ D₃) →
      ∀ A : EllipticCoeff (2+2) U, lam ≤ A.lam → A.Λ ≤ Lambda →
      (∀ x ∈ U, A.a x=c⁻¹ • complexCofactorCoeff u x) →
      ContDiffOn ℝ 4 u (ball x₀ delta) ∧
      (∀ x ∈ ball x₀ delta, ‖fderiv ℝ (fderiv ℝ (realHessian u)) x‖ ≤ Q) ∧
      ∀ x ∈ ball x₀ delta, ∀ y ∈ ball x₀ delta,
        ‖fderiv ℝ (fderiv ℝ (realHessian u)) x-
          fderiv ℝ (fderiv ℝ (realHessian u)) y‖ ≤ Q*‖x-y‖^alpha := by
  obtain ⟨delta,hd,hdr,Q,hQ,hupgrade⟩ := actual_uniform_C3_fourth_upgrade_of_second_weak_two
    hr hc hlam hLambda hH hM hK hD₂ hD₃ halpha ha1
  refine ⟨delta,hd,hdr,Q,hQ,?_⟩
  intro x₀ U hU hclosed u rho hu hrho hpos hdet hHess hthird hhold hD2 hD3 A hlo hhi hA
  exact hupgrade x₀ U hU hclosed u rho hu hrho hpos hHess hthird hhold hD2 hD3 A hlo hhi hA
    (fun v w => actual_C3_scaled_cofactor_second_variation_weak_ball_two hU hu
      (hrho.of_le (by norm_num)) hpos hdet A hA hclosed v w)

end PowerConvexity
