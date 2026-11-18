import PowerConvexity.Analysis.ActualCMAHigherInteriorTwo
import PowerConvexity.Calculus.ActualInteriorC4LimitFromModulus

/-! # Actual interior C4 limits with every higher estimate derived from C2 input -/
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

theorem actual_CMA_interior_C4_limit_from_uniform_C2_two
    {r c lam Lambda K P H D₁ D₂ D₃ alpha : ℝ}
    (hr : 0 < r) (hc : 0 < c) (hlam : 0 < lam) (hLambda : 0 < Lambda)
    (hK : 0 ≤ K) (hP : 0 ≤ P) (hH : 0 ≤ H)
    (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂) (hD₃ : 0 ≤ D₃)
    (halpha : 0 < alpha) (ha1 : alpha ≤ 1) :
    ∃ delta > 0, delta ≤ r/4 ∧
      ∀ x₀ : E, ∀ U : Set E, IsOpen U → closedBall x₀ (2*r) ⊆ U →
      ∀ u rho : ℕ → E → ℝ,
      (∀ n, ContDiffOn ℝ 4 (u n) U) → (∀ n, ContDiffOn ℝ 3 (rho n) U) →
      (∀ n x, x ∈ U → (complexHessian realDirections imagDirections (u n) x).PosDef) →
      (∀ n x, x ∈ U → (complexHessian realDirections imagDirections (u n) x).det = (rho n x : ℂ)) →
      (∀ n x, x ∈ U → ‖fderiv ℝ (u n) x‖ ≤ P) →
      (∀ n x, x ∈ U → ‖realHessian (u n) x‖ ≤ H) →
      (∀ n x, x ∈ U → ‖fderiv ℝ (rho n) x‖ ≤ D₁) →
      (∀ n x, x ∈ U → ‖realHessian (rho n) x‖ ≤ D₂) →
      (∀ n x, x ∈ U → ‖fderiv ℝ (realHessian (rho n)) x‖ ≤ D₃) →
      (∀ n x, x ∈ closedBall x₀ r → ∀ y, y ∈ closedBall x₀ r →
        ‖realHessian (u n) x-realHessian (u n) y‖ ≤ K*‖x-y‖^alpha) →
      (∀ n, ∃ A : EllipticCoeff (2+2) U, lam ≤ A.lam ∧ A.Λ ≤ Lambda ∧
        ∀ x ∈ U, A.a x = c⁻¹ • complexCofactorCoeff (u n) x) →
      ∀ g : E → ℝ, ContDiffOn ℝ 2 g U →
      (∀ x ∈ U, Tendsto (fun n => realHessian (u n) x) atTop (𝓝 (realHessian g x))) →
      ContDiffOn ℝ 4 g (ball x₀ delta) := by
  obtain ⟨d,hd,hdr,beta₃,beta₄,hbeta₃,hbeta₃1,hbeta₄,hbeta₄1,M₃,M₄,hM₃,hM₄,hjets⟩ :=
    actual_uniform_CMA_third_fourth_jets_from_C2_two hr hc hlam hLambda hK hP hH
      hD₁ hD₂ hD₃ halpha ha1
  refine ⟨d/4,by positivity,by linarith,?_⟩
  intro x₀ U hU hclosed u rho hu hrho hpos hdet hgrad hHess hD1 hD2 hD3 hhold hcoeff g hg hlim
  have hjet (n : ℕ) :
      (∀ x ∈ ball x₀ d, ‖fderiv ℝ (realHessian (u n)) x‖ ≤ M₃) ∧
      (∀ x ∈ ball x₀ d, ∀ y ∈ ball x₀ d,
        ‖fderiv ℝ (realHessian (u n)) x-fderiv ℝ (realHessian (u n)) y‖ ≤ M₃*‖x-y‖^beta₃) ∧
      (∀ x ∈ ball x₀ d, ‖fderiv ℝ (fderiv ℝ (realHessian (u n))) x‖ ≤ M₄) ∧
      ∀ x ∈ ball x₀ d, ∀ y ∈ ball x₀ d,
        ‖fderiv ℝ (fderiv ℝ (realHessian (u n))) x-
          fderiv ℝ (fderiv ℝ (realHessian (u n))) y‖ ≤ M₄*‖x-y‖^beta₄ := by
    obtain ⟨A,hlo,hhi,hA⟩ := hcoeff n
    exact hjets x₀ U hU hclosed (u n) (rho n) (hu n) (hrho n) (hpos n) (hdet n)
      (hgrad n) (hHess n) (hD1 n) (hD2 n) (hD3 n) (hhold n) A hlo hhi hA
  have hsmall : closedBall x₀ (d/2) ⊆ ball x₀ d := closedBall_subset_ball (by linarith)
  have hcl : closedBall x₀ (d/2) ⊆ U := hsmall.trans
    ((ball_subset_ball (by linarith : d ≤ 2*r)).trans (ball_subset_closedBall.trans hclosed))
  let omega₃ : ℝ → ℝ := fun a => M₃*|a|^beta₃
  let omega₄ : ℝ → ℝ := fun a => M₄*|a|^beta₄
  have ho₃ : Tendsto omega₃ (𝓝 0) (𝓝 0) := by
    have hh : Continuous omega₃ := continuous_const.mul
      ((Real.continuous_rpow_const hbeta₃.le).comp continuous_abs)
    simpa only [omega₃,abs_zero,Real.zero_rpow hbeta₃.ne',mul_zero] using hh.tendsto (0 : ℝ)
  have ho₄ : Tendsto omega₄ (𝓝 0) (𝓝 0) := by
    have hh : Continuous omega₄ := continuous_const.mul
      ((Real.continuous_rpow_const hbeta₄.le).comp continuous_abs)
    simpa only [omega₄,abs_zero,Real.zero_rpow hbeta₄.ne',mul_zero] using hh.tendsto (0 : ℝ)
  have hout := actual_interior_C4_limit_of_hessian_convergence hU u hu hg hlim
    (by positivity : 0 < d/2) hcl
    (fun n x hx => (hjet n).1 x (hsmall hx))
    (fun n x hx => (hjet n).2.2.1 x (hsmall hx)) omega₃ omega₄ ho₃ ho₄
    (fun n x hx y hy => by
      simpa only [omega₃,abs_of_nonneg (norm_nonneg _)] using
        (hjet n).2.1 x (hsmall hx) y (hsmall hy))
    (fun n x hx y hy => by
      simpa only [omega₄,abs_of_nonneg (norm_nonneg _)] using
        (hjet n).2.2.2 x (hsmall hx) y (hsmall hy))
  convert hout using 1 <;> congr 1 <;> ring

end PowerConvexity
