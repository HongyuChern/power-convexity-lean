import PowerConvexity.Analysis.ActualScalarQuadraticSequenceTwo
import Mathlib.Analysis.SpecificLimits.Normed

/-! # Actual limits of the constructed quadratic jets, with scale-sensitive tails.
The value, gradient and Hessian tails retain respectively two, one and
zero powers of the spatial scale. No jet of the weak solution is assumed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_geometric_increment_limit
    {X : Type*} [NormedAddCommGroup X] [CompleteSpace X]
    {v : ℕ → X} {M rho : ℝ} (hM : 0 ≤ M) (hrho : 0 ≤ rho) (hrho2 : rho ≤ 1/2)
    (hi : ∀ n, ‖v (n+1)-v n‖ ≤ M*rho^n) :
    ∃ a : X, Tendsto v atTop (𝓝 a) ∧ ∀ n, ‖v n-a‖ ≤ 2*M*rho^n := by
  have hrho1 : rho < 1 := by linarith
  have hd (n : ℕ) : dist (v n) (v (n+1)) ≤ M*rho^n := by
    rw [dist_comm,dist_eq_norm]
    exact hi n
  obtain ⟨a,ha⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric rho M hrho1 hd)
  refine ⟨a,ha,?_⟩
  intro n
  have hh := dist_le_of_le_geometric_of_tendsto rho M hrho1 hd ha n
  have hn : 0 ≤ M*rho^n := mul_nonneg hM (pow_nonneg hrho n)
  have hden : 0 < 1-rho := by linarith
  have hb : M*rho^n/(1-rho) ≤ 2*M*rho^n := by
    apply (div_le_iff₀ hden).2
    nlinarith [mul_le_mul_of_nonneg_left hrho2 hn]
  simpa only [dist_eq_norm] using hh.trans hb

theorem actual_scalar_quadratic_jet_limits_two
    {M r : ℝ} (hM : 0 ≤ M) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    {Q : ℕ → E → ℝ}
    (hi : ∀ n, ActualScalarQuadraticIncrementTwo M r n (Q n) (Q (n+1))) :
    ∃ (c : ℝ) (l : E →L[ℝ] ℝ) (H : E →L[ℝ] E →L[ℝ] ℝ),
      Tendsto (fun n => Q n 0) atTop (𝓝 c) ∧
      Tendsto (fun n => fderiv ℝ (Q n) 0) atTop (𝓝 l) ∧
      Tendsto (fun n => realHessian (Q n) 0) atTop (𝓝 H) ∧
      (∀ n, |Q n 0-c| ≤ 2*M*(1/2 : ℝ)^n*(r^n)^2) ∧
      (∀ n, ‖fderiv ℝ (Q n) 0-l‖ ≤ 2*M*(1/2 : ℝ)^n*r^n) ∧
      (∀ n, ‖realHessian (Q n) 0-H‖ ≤ 2*M*(1/2 : ℝ)^n) := by
  have hr2 : r^2 ≤ 1 := by nlinarith
  have he0 (n : ℕ) : ((1/2 : ℝ)*r^2)^n = (1/2 : ℝ)^n*(r^n)^2 := by
    rw [mul_pow,← pow_mul, Nat.mul_comm 2 n,pow_mul]
  have he1 (n : ℕ) : ((1/2 : ℝ)*r)^n = (1/2 : ℝ)^n*r^n := mul_pow _ _ _
  have hi0 (n : ℕ) : ‖Q (n+1) 0-Q n 0‖ ≤ M*((1/2 : ℝ)*r^2)^n := by
    rw [Real.norm_eq_abs,he0]
    exact (hi n).1.trans_eq (by ring)
  have hi1 (n : ℕ) : ‖fderiv ℝ (Q (n+1)) 0-fderiv ℝ (Q n) 0‖ ≤ M*((1/2 : ℝ)*r)^n := by
    rw [he1]
    exact (hi n).2.1.trans_eq (by ring)
  have hi2 (n : ℕ) : ‖realHessian (Q (n+1)) 0-realHessian (Q n) 0‖ ≤ M*(1/2 : ℝ)^n := by
    exact ((hi n).2.2 0).trans_eq (mul_comm _ _)
  obtain ⟨c,hc,hcB⟩ := actual_geometric_increment_limit (X := ℝ) (v := fun n => Q n 0) hM (by positivity : 0 ≤ (1/2 : ℝ)*r^2)
    (by nlinarith : (1/2 : ℝ)*r^2 ≤ 1/2) hi0
  obtain ⟨l,hl,hlB⟩ := actual_geometric_increment_limit (X := E →L[ℝ] ℝ) (v := fun n => fderiv ℝ (Q n) 0) hM (by positivity : 0 ≤ (1/2 : ℝ)*r)
    (by nlinarith : (1/2 : ℝ)*r ≤ 1/2) hi1
  obtain ⟨H,hH,hHB⟩ := actual_geometric_increment_limit (X := E →L[ℝ] E →L[ℝ] ℝ) (v := fun n => realHessian (Q n) 0) hM (by norm_num : 0 ≤ (1/2 : ℝ))
    (le_refl (1/2 : ℝ)) hi2
  refine ⟨c,l,H,hc,hl,hH,?_,?_,hHB⟩
  · intro n
    have hh := hcB n
    rw [Real.norm_eq_abs,he0] at hh
    exact hh.trans_eq (by ring)
  · intro n
    have hh := hlB n
    rw [he1] at hh
    exact hh.trans_eq (by ring)

end PowerConvexity
