import PowerConvexity.Analysis.ActualFlatDriftLimitExpansionFour

/-! # Uniform actual boundary expansion for a normalized full drift equation -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_flat_drift_normalized_quadratic_expansion_four {lam Lambda alpha : ℝ}
    (hlam : 0 < lam) (hLambda : 0 < Lambda) (halpha : 0 < alpha) (halpha1 : alpha ≤ 1) :
    ∃ C > 0, ∃ r > 0, r ≤ (1/8 : ℝ) ∧ r^alpha ≤ (1/2 : ℝ) ∧
      ∀ N : E, ‖N‖=1 → ∃ kappa > 0, kappa ≤ 1 ∧
      ∀ D : ActualFlatDriftIterationInputFour N lam Lambda alpha kappa, D.source 0=0 →
      ∃ p : E → ℝ, IsQuadraticPolynomial p ∧
        (∀ x : E, inner ℝ N x=0 → p x=0) ∧
        (realBlockHessian realDirections imagDirections p 0).trace+
          fderiv ℝ p 0 (D.drift 0) = -D.source 0 ∧
        ‖fderiv ℝ p 0‖ ≤ C ∧ (∀ x, ‖realHessian p x‖ ≤ C) ∧
        ∀ n : ℕ, ∀ x ∈ actualFlatClosedUpperBallFour N (r^n),
          |D.solution x-p x| ≤ C*(1/2 : ℝ)^n*(r^n)^2 := by
  obtain ⟨M,hM,r,hr,hr8,hrp,K,hK,hseq⟩ :=
    actual_flat_drift_quadratic_sequence_four hlam hLambda halpha halpha1
  have hr1 : r ≤ 1 := hr8.trans (by norm_num)
  let C := M+K
  have hC : 0 < C := add_pos hM hK
  refine ⟨1+7*C,by positivity,r,hr,hr8,hrp,?_⟩
  intro N hN
  obtain ⟨kappa,hk,hk1,hS⟩ := hseq N hN
  refine ⟨kappa,hk,hk1,?_⟩
  intro D hf0
  obtain ⟨S,hS0,hinc⟩ := hS D hf0
  obtain ⟨p,hp,hp0,hpt,hpD,hpH,herr⟩ := actual_flat_drift_sequence_limit_expansion_four
    hr hr1 hC.le S hS0 (actual_flat_drift_sequence_fullJet_increments_four hr hM hK S hinc)
  refine ⟨p,hp,hp0,hpt,hpD.trans (by linarith),fun x => (hpH x).trans (by linarith),?_⟩
  intro n x hx
  exact (herr n x hx).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by linarith : 1+5*C ≤ 1+7*C) (by positivity)) (sq_nonneg _))

end PowerConvexity
