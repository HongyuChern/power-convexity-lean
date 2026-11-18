import PowerConvexity.Analysis.ActualCMAThirdDerivativeEstimateTwo
import PowerConvexity.Analysis.ActualCMAFourthDerivativeEstimateTwo

/-! # Uniform third and fourth jets from the original actual C2 data -/
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

theorem actual_uniform_CMA_third_fourth_jets_from_C2_two
    {r c lam Lambda K P H D₁ D₂ D₃ alpha : ℝ}
    (hr : 0 < r) (hc : 0 < c) (hlam : 0 < lam) (hLambda : 0 < Lambda)
    (hK : 0 ≤ K) (hP : 0 ≤ P) (hH : 0 ≤ H)
    (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂) (hD₃ : 0 ≤ D₃)
    (halpha : 0 < alpha) (ha1 : alpha ≤ 1) :
    ∃ delta > 0, delta ≤ r/4 ∧
      ∃ beta₃ beta₄ : ℝ, 0 < beta₃ ∧ beta₃ < 1 ∧ 0 < beta₄ ∧ beta₄ < 1 ∧
      ∃ M₃ M₄ : ℝ, 0 ≤ M₃ ∧ 0 ≤ M₄ ∧
      ∀ x₀ : E, ∀ U : Set E, IsOpen U → closedBall x₀ (2*r) ⊆ U →
      ∀ u rho : E → ℝ, ContDiffOn ℝ 4 u U → ContDiffOn ℝ 3 rho U →
      (∀ x ∈ U, (complexHessian realDirections imagDirections u x).PosDef) →
      (∀ x ∈ U, (complexHessian realDirections imagDirections u x).det = (rho x : ℂ)) →
      (∀ x ∈ U, ‖fderiv ℝ u x‖ ≤ P) →
      (∀ x ∈ U, ‖realHessian u x‖ ≤ H) →
      (∀ x ∈ U, ‖fderiv ℝ rho x‖ ≤ D₁) →
      (∀ x ∈ U, ‖realHessian rho x‖ ≤ D₂) →
      (∀ x ∈ U, ‖fderiv ℝ (realHessian rho) x‖ ≤ D₃) →
      (∀ x ∈ closedBall x₀ r, ∀ y ∈ closedBall x₀ r,
        ‖realHessian u x-realHessian u y‖ ≤ K*‖x-y‖^alpha) →
      ∀ A : EllipticCoeff (2+2) U, lam ≤ A.lam → A.Λ ≤ Lambda →
      (∀ x ∈ U, A.a x = c⁻¹ • complexCofactorCoeff u x) →
      (∀ x ∈ ball x₀ delta, ‖fderiv ℝ (realHessian u) x‖ ≤ M₃) ∧
      (∀ x ∈ ball x₀ delta, ∀ y ∈ ball x₀ delta,
        ‖fderiv ℝ (realHessian u) x-fderiv ℝ (realHessian u) y‖ ≤ M₃*‖x-y‖^beta₃) ∧
      (∀ x ∈ ball x₀ delta, ‖fderiv ℝ (fderiv ℝ (realHessian u)) x‖ ≤ M₄) ∧
      ∀ x ∈ ball x₀ delta, ∀ y ∈ ball x₀ delta,
        ‖fderiv ℝ (fderiv ℝ (realHessian u)) x-
          fderiv ℝ (fderiv ℝ (realHessian u)) y‖ ≤ M₄*‖x-y‖^beta₄ := by
  obtain ⟨delta₃,hd₃,hdr₃,beta₃,hbeta₃,hbeta₃1,M₃,hM₃,hthird⟩ :=
    actual_uniform_CMA_third_derivative_holder_two hr hc hlam hLambda hK hP hD₁ hD₂ halpha ha1
  let r₄ := delta₃/4
  have hr₄ : 0 < r₄ := by dsimp [r₄]; positivity
  obtain ⟨delta₄,hd₄,hdr₄,beta₄,hbeta₄,hbeta₄1,M₄,hM₄,hfourth⟩ :=
    actual_uniform_CMA_fourth_derivative_holder_two hr₄ hc hlam hLambda hH hM₃ hM₃
      hD₂ hD₃ hbeta₃ hbeta₃1.le
  have hd₄₃ : delta₄ ≤ delta₃ := by dsimp only [r₄] at hdr₄; linarith
  refine ⟨delta₄,hd₄,hd₄₃.trans hdr₃,beta₃,beta₄,hbeta₃,hbeta₃1,hbeta₄,hbeta₄1,M₃,M₄,hM₃,hM₄,?_⟩
  intro x₀ U hU hclosed u rho hu hrho hpos hdet hgrad hHess hD1 hD2 hD3 hhold A hlo hhi hA
  obtain ⟨hb₃,hm₃⟩ := hthird x₀ U hU hclosed u rho hu (hrho.of_le (by norm_num))
    hpos hdet hgrad hD1 hD2 hhold A hlo hhi hA
  have hsub₃ : ball x₀ delta₃ ⊆ U :=
    (ball_subset_ball (by linarith : delta₃ ≤ 2*r)).trans (ball_subset_closedBall.trans hclosed)
  have hclosed₄ : closedBall x₀ (2*r₄) ⊆ ball x₀ delta₃ :=
    closedBall_subset_ball (by dsimp only [r₄]; linarith)
  have hb₄sub : ball x₀ (2*r₄) ⊆ ball x₀ delta₃ := ball_subset_closedBall.trans hclosed₄
  obtain ⟨hb₄,hm₄⟩ := hfourth x₀ (ball x₀ delta₃) isOpen_ball hclosed₄ u rho
    (hu.mono hsub₃) (hrho.mono hsub₃) (fun x hx => hpos x (hsub₃ hx))
    (fun x hx => hdet x (hsub₃ hx)) (fun x hx => hHess x (hsub₃ hx)) hb₃
    (fun x hx y hy => hm₃ x (hb₄sub hx) y (hb₄sub hy))
    (fun x hx => hD2 x (hsub₃ hx)) (fun x hx => hD3 x (hsub₃ hx))
    (A.restrict hsub₃) hlo hhi (fun x hx => hA x (hsub₃ hx))
  have hsm : ball x₀ delta₄ ⊆ ball x₀ delta₃ := ball_subset_ball hd₄₃
  exact ⟨fun x hx => hb₃ x (hsm hx),fun x hx y hy => hm₃ x (hsm hx) y (hsm hy),hb₄,hm₄⟩

end PowerConvexity
