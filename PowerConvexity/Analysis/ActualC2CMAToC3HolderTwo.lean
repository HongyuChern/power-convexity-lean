import PowerConvexity.Analysis.ActualC2CMAFirstWeakResponseTwo
import PowerConvexity.Analysis.ActualC3FromFirstWeakVariationTwo

/-! # The genuine C2 Monge-Ampere solution upgrades to C3 with Holder third jet

All first-variation equations are proved from the same C2 determinant
solution.  Constants precede the potential and preserve its input exponent.
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

theorem actual_uniform_C2_CMA_C3_holder_two
    {r c lam Lambda K P D₁ D₂ alpha : ℝ}
    (hr : 0 < r) (hc : 0 < c) (hlam : 0 < lam) (hLambda : 0 < Lambda)
    (hK : 0 ≤ K) (hP : 0 ≤ P) (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂)
    (halpha : 0 < alpha) (halpha1 : alpha < 1) :
    ∃ delta > 0, delta ≤ r/4 ∧ ∃ M ≥ 0,
      ∀ x₀ : E, ∀ U : Set E, IsOpen U → closedBall x₀ (4*r) ⊆ U →
      ∀ u rho : E → ℝ, ContDiffOn ℝ 2 u U → ContDiffOn ℝ 2 rho U →
      (∀ x ∈ U, (complexHessian realDirections imagDirections u x).PosDef) →
      (∀ x ∈ U, (complexHessian realDirections imagDirections u x).det=(rho x : ℂ)) →
      (∀ x ∈ U, ‖fderiv ℝ u x‖ ≤ P) →
      (∀ x ∈ U, ‖fderiv ℝ rho x‖ ≤ D₁) →
      (∀ x ∈ U, ‖realHessian rho x‖ ≤ D₂) →
      (∀ x ∈ closedBall x₀ r, ∀ y ∈ closedBall x₀ r,
        ‖realHessian u x-realHessian u y‖ ≤ K*‖x-y‖^alpha) →
      ∀ A : EllipticCoeff (2+2) U, lam ≤ A.lam → A.Λ ≤ Lambda →
      (∀ x ∈ U, A.a x=c⁻¹ • complexCofactorCoeff u x) →
      ContDiffOn ℝ 3 u (ball x₀ delta) ∧
      (∀ x ∈ ball x₀ delta, ‖fderiv ℝ (realHessian u) x‖ ≤ M) ∧
      ∀ x ∈ ball x₀ delta, ∀ y ∈ ball x₀ delta,
        ‖fderiv ℝ (realHessian u) x-fderiv ℝ (realHessian u) y‖ ≤ M*‖x-y‖^alpha := by
  obtain ⟨delta,hd,hdr,M,hM,hupgrade⟩ :=
    actual_uniform_C3_from_first_cofactor_weak_two hr hc hlam hLambda hK hP hD₁ hD₂ halpha halpha1
  refine ⟨delta,hd,hdr,M,hM,?_⟩
  intro x₀ U hU hclosed u rho hu hrho hpos hdet hgrad hD1 hD2 hhold A hlo hhi hA
  have hsmall : closedBall x₀ (2*r) ⊆ U :=
    (closedBall_subset_closedBall (by linarith : 2*r ≤ 4*r)).trans hclosed
  apply hupgrade x₀ U hU hsmall u rho hu hrho hpos hgrad hD1 hD2 hhold A hlo hhi hA
  intro v hv
  apply actual_C2_scaled_cofactor_first_variation_weak_ball_two hU hu
    (hrho.of_le (by norm_num)) ?_ A hA (by positivity : 0 < 2*r)
    (by linarith : 2*r < 4*r) hclosed v
  intro x hx
  rw [hdet x hx,Complex.ofReal_re]

end PowerConvexity
