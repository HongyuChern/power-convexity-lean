import PowerConvexity.Analysis.ActualFlatDriftNormalizedExpansionFour

/-! # Removing the actual constant source while retaining the full drift -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_flat_source_quadratic_full_frozen_four {N : E} (hN : ‖N‖=1)
    (f0 : ℝ) (b0 : E) :
    (realBlockHessian realDirections imagDirections (actualFlatSourceQuadraticFour N f0) 0).trace+
      fderiv ℝ (actualFlatSourceQuadraticFour N f0) 0 b0 = -f0 := by
  rw [actual_flat_source_quadratic_trace_four hN,actualFlatSourceQuadraticFour_fderiv_zero]
  simp only [_root_.zero_apply,add_zero]

theorem actual_flat_drift_corrected_source_growth_four {N : E} (hN : ‖N‖=1)
    {lam Lambda alpha kappa F a : ℝ} (halpha : 0 < alpha) (halpha1 : alpha ≤ 1)
    (hk : 0 ≤ kappa) (hF : 0 ≤ F) (ha : 0 < a)
    (D : ActualFlatDriftIterationInputFour N lam Lambda alpha kappa) (hf0 : |D.source 0| ≤ F) :
    ∀ x ∈ actualFlatUpperBallFour N 1,
      |actualFlatDriftResidualSourceFour D.coeff.a D.drift D.source
        (actualFlatSourceQuadraticFour N (D.source 0)) 1 a x| ≤
      (a⁻¹*kappa*(1+17*F))*‖x‖^alpha := by
  intro x hx
  let q := actualFlatSourceQuadraticFour N (D.source 0)
  have hq := actualFlatSourceQuadraticFour_quadratic N (D.source 0)
  have hH : ‖realHessian q 0‖ ≤ F := (actualFlatSourceQuadraticFour_hessian_norm hN _ 0).le.trans hf0
  have hD : ‖fderiv ℝ q 0‖ ≤ (0 : ℝ) := by rw [actualFlatSourceQuadraticFour_fderiv_zero,norm_zero]
  have hh := actual_full_drift_residual_holder_growth_four D.coeff.a D.drift D.source hq
    hk hk hk hF (le_refl 0) hH hD (actual_flat_source_quadratic_full_frozen_four hN _ _)
    D.growth D.drift_growth D.drift_bound D.source_growth x hx
  have hxn : ‖x‖ ≤ 1 := (show ‖x‖ < 1 from by simpa only [mem_ball,dist_zero_right] using hx.1).le
  have hxp : ‖x‖ ≤ ‖x‖^alpha := Real.self_le_rpow_of_le_one (norm_nonneg _) hxn halpha1
  have hh' : |D.source x-quadraticScalarSourceTwo D.coeff.a q x+fderiv ℝ q x (D.drift x)| ≤
      (kappa*(1+17*F))*‖x‖^alpha := by
    apply hh.trans
    have hm := mul_le_mul_of_nonneg_left hxp (mul_nonneg hF hk)
    nlinarith
  simp only [actualFlatDriftResidualSourceFour,one_smul,abs_mul,abs_of_pos (inv_pos.mpr ha)]
  exact (mul_le_mul_of_nonneg_left hh' (inv_pos.mpr ha).le).trans_eq (by ring)

def actualFlatDriftRemoveSourceFour {N : E} (hN : ‖N‖=1)
    {lam Lambda alpha kappa tau F a : ℝ} (halpha : 0 < alpha) (halpha1 : alpha ≤ 1)
    (hk : 0 ≤ kappa) (hF : 0 ≤ F) (ha : 0 < a) (hkt : kappa ≤ tau)
    (hsize : 1+F/2 ≤ a) (hsource : a⁻¹*kappa*(1+17*F) ≤ tau)
    (D : ActualFlatDriftIterationInputFour N lam Lambda alpha kappa) (hf0 : |D.source 0| ≤ F) :
    ActualFlatDriftIterationInputFour N lam Lambda alpha tau := by
  let q := actualFlatSourceQuadraticFour N (D.source 0)
  have hq := actualFlatSourceQuadraticFour_quadratic N (D.source 0)
  have hq0 (x : E) (hx : inner ℝ N x=0) : q x=0 := actualFlatSourceQuadraticFour_zero N _ hx
  have hreg := actual_flat_residual_regularity_four (R := 1) (b := a) zero_lt_one le_rfl hq
    D.solution_regular D.solution_continuous D.solution_zero hq0
  have hsrc0 : actualFlatDriftResidualSourceFour D.coeff.a D.drift D.source q 1 a 0=0 :=
    actual_flat_drift_residual_source_zero_four (actual_flat_drift_input_frozen_four hN halpha D)
      (actual_flat_source_quadratic_full_frozen_four hN _ _) 1 a
  have herr : ∀ x ∈ actualFlatClosedUpperBallFour N 1, |D.solution x-q x| ≤ a*1^2 := by
    intro x hx
    have hxn : ‖x‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using hx.1
    have hqv : |q x| ≤ F/2 :=
      (actualFlatSourceQuadraticFour_value_bound hN _ x).trans
        ((mul_le_mul (div_le_div_of_nonneg_right hf0 (by norm_num))
          (pow_le_pow_left₀ (norm_nonneg _) hxn 2) (sq_nonneg _) (by positivity)).trans_eq (by norm_num))
    have hh := (abs_sub _ _).trans ((add_le_add (D.solution_bound x hx) hqv).trans hsize)
    simpa only [one_pow,mul_one] using hh
  exact {
    coeff := D.coeff
    drift := D.drift
    source := actualFlatDriftResidualSourceFour D.coeff.a D.drift D.source q 1 a
    solution := normalizedScalarResidualTwo D.solution q 1 a
    lower := D.lower
    upper := D.upper
    positive := D.positive
    regular := D.regular
    continuous := D.continuous
    divergence := D.divergence
    growth := fun x hx => (D.growth x hx).trans
      (mul_le_mul_of_nonneg_right hkt (Real.rpow_nonneg (norm_nonneg _) alpha))
    drift_continuous := D.drift_continuous
    drift_bound := fun x hx => (D.drift_bound x hx).trans hkt
    drift_growth := fun x hx => (D.drift_growth x hx).trans
      (mul_le_mul_of_nonneg_right hkt (Real.rpow_nonneg (norm_nonneg _) alpha))
    source_continuous := actual_flat_drift_residual_continuous_four zero_lt_one le_rfl
      D.continuous D.drift_continuous D.source_continuous hq
    source_growth := by
      intro x hx
      rw [hsrc0,sub_zero]
      exact (actual_flat_drift_corrected_source_growth_four hN halpha halpha1 hk hF ha D hf0 x hx).trans
        (mul_le_mul_of_nonneg_right hsource (Real.rpow_nonneg (norm_nonneg _) alpha))
    solution_regular := hreg.1
    solution_continuous := hreg.2.1
    solution_zero := hreg.2.2
    solution_bound := actual_flat_residual_bound_four zero_lt_one ha herr
    equation := by
      intro x hx
      simpa only [one_smul] using actual_normalized_residual_drift_equation_four
        (actualFlatUpperBallFour_isOpen N 1) (R := 1) (a := a) zero_lt_one D.solution_regular hq D.equation x
        (by simpa only [one_smul] using hx)
  }

end PowerConvexity
