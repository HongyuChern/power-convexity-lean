import PowerConvexity.Calculus.ActualInteriorC1LimitFromModulus
import PowerConvexity.Calculus.ActualFourthJetNormTwo

/-! # Actual C4 interior limit from uniform third and fourth derivative moduli -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
attribute [local instance] atjInstance1 atjInstance2 atjInstance3 atjInstance4 atjInstance5 atjInstance6
attribute [local instance] ahdTripleNormedGroup ahdTripleNormedSpace ahdTripleModule ahdTripleTopology
local instance ac4FiniteFirst : FiniteDimensional ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.finiteDimensional
local instance ac4FiniteSecond : FiniteDimensional ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.finiteDimensional
local instance ac4FiniteThird : FiniteDimensional ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.finiteDimensional

theorem actual_interior_C4_limit_of_hessian_convergence
    {U : Set E} (hU : IsOpen U) (u : ℕ → E → ℝ)
    (hu : ∀ n, ContDiffOn ℝ 4 (u n) U) {g : E → ℝ} (hg : ContDiffOn ℝ 2 g U)
    (hlim : ∀ x ∈ U, Tendsto (fun n => realHessian (u n) x) atTop (𝓝 (realHessian g x)))
    {x₀ : E} {R M₃ M₄ : ℝ} (hR : 0 < R) (hclosed : closedBall x₀ R ⊆ U)
    (hbound₃ : ∀ n x, x ∈ closedBall x₀ R → ‖fderiv ℝ (realHessian (u n)) x‖ ≤ M₃)
    (hbound₄ : ∀ n x, x ∈ closedBall x₀ R → ‖fderiv ℝ (fderiv ℝ (realHessian (u n))) x‖ ≤ M₄)
    (omega₃ omega₄ : ℝ → ℝ)
    (homega₃ : Tendsto omega₃ (𝓝 0) (𝓝 0)) (homega₄ : Tendsto omega₄ (𝓝 0) (𝓝 0))
    (hmod₃ : ∀ n x, x ∈ closedBall x₀ R → ∀ y, y ∈ closedBall x₀ R →
      ‖fderiv ℝ (realHessian (u n)) x-fderiv ℝ (realHessian (u n)) y‖ ≤ omega₃ ‖x-y‖)
    (hmod₄ : ∀ n x, x ∈ closedBall x₀ R → ∀ y, y ∈ closedBall x₀ R →
      ‖fderiv ℝ (fderiv ℝ (realHessian (u n))) x-
        fderiv ℝ (fderiv ℝ (realHessian (u n))) y‖ ≤ omega₄ ‖x-y‖) :
    ContDiffOn ℝ 4 g (ball x₀ (R/2)) := by
  have hH (n : ℕ) : ContDiffOn ℝ 2 (realHessian (u n)) U :=
    ((hu n).fderiv_of_isOpen hU (m := 3) (by norm_num)).fderiv_of_isOpen hU (m := 2) (by norm_num)
  obtain ⟨hgH1,phi,hphi,hTlim,_,_⟩ := actual_interior_C1_limit_of_derivative_modulus
    hU (fun n => realHessian (u n)) (fun n => (hH n).of_le (by norm_num))
      hlim hR hclosed hbound₃ omega₃ homega₃ hmod₃
  have hsmall : closedBall x₀ (R/2) ⊆ ball x₀ R := closedBall_subset_ball (by linarith)
  have hsmaller : closedBall x₀ (R/2) ⊆ closedBall x₀ R := closedBall_subset_closedBall (by linarith)
  have hball : ball x₀ R ⊆ U := ball_subset_closedBall.trans hclosed
  have hT (n : ℕ) : ContDiffOn ℝ 1 (fderiv ℝ (realHessian (u (phi n)))) (ball x₀ R) :=
    ((hH (phi n)).fderiv_of_isOpen hU (m := 1) (by norm_num)).mono hball
  obtain ⟨hgT1,_,_,_,_,_⟩ := actual_interior_C1_limit_of_derivative_modulus
    isOpen_ball (fun n => fderiv ℝ (realHessian (u (phi n)))) hT
      (fun x hx => hTlim.tendsto_at hx) (by positivity : 0 < R/2) hsmall
      (fun n x hx => hbound₄ (phi n) x (hsmaller hx)) omega₄ homega₄
      (fun n x hx y hy => hmod₄ (phi n) x (hsmaller hx) y (hsmaller hy))
  have hb : ball x₀ (R/2) ⊆ ball x₀ R := ball_subset_ball (by linarith)
  have hgH2 : ContDiffOn ℝ 2 (realHessian g) (ball x₀ (R/2)) := by
    rw [show (2 : ℕ∞ω) = 1+1 by norm_num,contDiffOn_succ_iff_fderiv_of_isOpen isOpen_ball]
    exact ⟨(hgH1.mono hb).differentiableOn (by norm_num),by simp,hgT1⟩
  have hgD3 : ContDiffOn ℝ 3 (fderiv ℝ g) (ball x₀ (R/2)) := by
    rw [show (3 : ℕ∞ω) = 2+1 by norm_num,contDiffOn_succ_iff_fderiv_of_isOpen isOpen_ball]
    exact ⟨((hg.fderiv_of_isOpen hU (m := 1) (by norm_num)).mono (hb.trans hball)).differentiableOn
      (by norm_num),by simp,hgH2⟩
  rw [show (4 : ℕ∞ω) = 3+1 by norm_num,contDiffOn_succ_iff_fderiv_of_isOpen isOpen_ball]
  exact ⟨(hg.mono (hb.trans hball)).differentiableOn (by norm_num),by simp,hgD3⟩

end PowerConvexity
