import PowerConvexity.Analysis.ActualFlatQuadraticLimitFour

/-! # Uniform actual boundary expansion for the normalized equation
Every constant is selected before the actual coefficient, source and solution.
The smallness threshold may depend on the fixed unit normal.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_flat_normalized_quadratic_expansion_four {lam Lambda alpha : ℝ}
    (hlam : 0 < lam) (hLambda : 0 < Lambda) (halpha : 0 < alpha) :
    ∃ K > 0, ∃ r > 0, r ≤ (1/8 : ℝ) ∧ r^alpha ≤ (1/2 : ℝ) ∧
      ∀ N : E, ‖N‖=1 → ∃ kappa > 0, kappa ≤ 1 ∧
      ∀ D : ActualFlatIterationInputFour N lam Lambda alpha kappa,
      ∃ p : E → ℝ, IsQuadraticPolynomial p ∧
        (∀ x : E, inner ℝ N x=0 → p x=0) ∧
        (∀ x, (realBlockHessian realDirections imagDirections p x).trace=0) ∧
        ‖fderiv ℝ p 0‖ ≤ K ∧ (∀ x, ‖realHessian p x‖ ≤ K) ∧
        ∀ n : ℕ, ∀ x ∈ actualFlatClosedUpperBallFour N (r^n),
          |D.solution x-p x| ≤ K*(1/2 : ℝ)^n*(r^n)^2 := by
  obtain ⟨M,hM,r,hr,hr8,hrp,hseq⟩ := actual_flat_quadratic_sequence_four hlam hLambda halpha
  have hr1 : r ≤ 1 := by linarith
  obtain ⟨C,hC,hinc⟩ := actual_flat_sequence_fullJet_increments_four hr hr1 hM
  refine ⟨1+7*C,by positivity,r,hr,hr8,hrp,?_⟩
  intro N hN
  obtain ⟨kappa,hk,hk1,hS⟩ := hseq N hN
  refine ⟨kappa,hk,hk1,?_⟩
  intro D
  obtain ⟨S,hS0,hSH⟩ := hS D
  obtain ⟨p,hp,hp0,hpt,hpD,hpH,herr⟩ := actual_flat_sequence_limit_expansion_four hr hr1 hC.le
    S hS0 (hinc N hN D.solution S hSH)
  refine ⟨p,hp,hp0,hpt,hpD.trans (by linarith),fun x => (hpH x).trans (by linarith),?_⟩
  intro n x hx
  exact (herr n x hx).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by linarith : 1+5*C ≤ 1+7*C) (by positivity)) (sq_nonneg _))

end PowerConvexity
