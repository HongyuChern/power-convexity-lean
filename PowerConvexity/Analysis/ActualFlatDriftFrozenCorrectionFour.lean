import PowerConvexity.Analysis.ActualFlatFrozenEquationFour

/-! # A flat-boundary correction for the full frozen equation, including drift -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

def actualFlatDriftCorrectedPolynomialFour (N b : E) (f : ℝ) (p : E → ℝ) : E → ℝ :=
  p+actualFlatSourceQuadraticFour N (f+fderiv ℝ p 0 b)

theorem actual_flat_drift_corrected_quadratic_four (N b : E) (f : ℝ)
    {p : E → ℝ} (hp : IsQuadraticPolynomial p) :
    IsQuadraticPolynomial (actualFlatDriftCorrectedPolynomialFour N b f p) :=
  IsQuadraticPolynomial_add hp (actualFlatSourceQuadraticFour_quadratic N _)

theorem actual_flat_drift_corrected_zero_four (N b : E) (f : ℝ)
    {p : E → ℝ} (hp0 : ∀ x : E, inner ℝ N x=0 → p x=0)
    {x : E} (hx : inner ℝ N x=0) :
    actualFlatDriftCorrectedPolynomialFour N b f p x=0 := by
  simp only [actualFlatDriftCorrectedPolynomialFour,Pi.add_apply,hp0 x hx,
    actualFlatSourceQuadraticFour_zero N _ hx,add_zero]

theorem actual_flat_drift_corrected_first_jet_four (N b : E) (f : ℝ)
    {p : E → ℝ} (hp : IsQuadraticPolynomial p) :
    fderiv ℝ (actualFlatDriftCorrectedPolynomialFour N b f p) 0=fderiv ℝ p 0 := by
  have hd := (IsQuadraticPolynomial_contDiff hp 1).differentiable (by norm_num)
  have hc := (IsQuadraticPolynomial_contDiff
    (actualFlatSourceQuadraticFour_quadratic N (f+fderiv ℝ p 0 b)) 1).differentiable (by norm_num)
  rw [actualFlatDriftCorrectedPolynomialFour,fderiv_add hd.differentiableAt hc.differentiableAt,
    actualFlatSourceQuadraticFour_fderiv_zero,add_zero]

theorem actual_flat_drift_corrected_hessian_four (N b : E) (f : ℝ)
    {p : E → ℝ} (hp : IsQuadraticPolynomial p) (x : E) :
    realHessian (actualFlatDriftCorrectedPolynomialFour N b f p) x =
      realHessian p x+(-(f+fderiv ℝ p 0 b)) • realRankOneForm N := by
  change realHessian (fun y => p y+actualFlatSourceQuadraticFour N (f+fderiv ℝ p 0 b) y) x = _
  rw [realHessian_add (IsQuadraticPolynomial_contDiff hp 2).contDiffAt
      (IsQuadraticPolynomial_contDiff (actualFlatSourceQuadraticFour_quadratic N _) 2).contDiffAt,
    actualFlatSourceQuadraticFour_hessian]

theorem actual_flat_drift_corrected_frozen_equation_four {N : E} (hN : ‖N‖=1)
    (b : E) (f : ℝ) {p : E → ℝ} (hp : IsQuadraticPolynomial p)
    (ht : (realBlockHessian realDirections imagDirections p 0).trace=0) :
    (realBlockHessian realDirections imagDirections
      (actualFlatDriftCorrectedPolynomialFour N b f p) 0).trace+
      fderiv ℝ (actualFlatDriftCorrectedPolynomialFour N b f p) 0 b = -f := by
  have he : realBlockHessian realDirections imagDirections
      (actualFlatDriftCorrectedPolynomialFour N b f p) 0 =
      realBlockHessian realDirections imagDirections p 0+
      realBlockHessian realDirections imagDirections
        (actualFlatSourceQuadraticFour N (f+fderiv ℝ p 0 b)) 0 := by
    ext i j
    simp only [realBlockHessian,actual_flat_drift_corrected_hessian_four N b f hp,
      actualFlatSourceQuadraticFour_hessian,ContinuousLinearMap.add_apply,Matrix.add_apply]
  rw [he,Matrix.trace_add,ht,actual_flat_source_quadratic_trace_four hN,
    actual_flat_drift_corrected_first_jet_four N b f hp]
  ring

theorem actual_flat_drift_correction_coefficient_bound_four {b : E} {f delta : ℝ}
    (hf : |f| ≤ delta) (hb : ‖b‖ ≤ delta) (p : E → ℝ) :
    |f+fderiv ℝ p 0 b| ≤ delta*(1+‖fderiv ℝ p 0‖) := by
  calc
    _ ≤ |f|+|fderiv ℝ p 0 b| := by simpa only [Real.norm_eq_abs] using norm_add_le f (fderiv ℝ p 0 b)
    _ ≤ delta+‖fderiv ℝ p 0‖*delta := add_le_add hf
      (((fderiv ℝ p 0).le_opNorm b).trans (mul_le_mul_of_nonneg_left hb (norm_nonneg _)))
    _ = _ := by ring

theorem actual_flat_drift_correction_value_bound_four {N b : E} (hN : ‖N‖=1)
    {f delta : ℝ} (hf : |f| ≤ delta) (hb : ‖b‖ ≤ delta) (p : E → ℝ) (x : E) :
    |actualFlatDriftCorrectedPolynomialFour N b f p x-p x| ≤
      (delta*(1+‖fderiv ℝ p 0‖)/2)*‖x‖^2 := by
  have he : actualFlatDriftCorrectedPolynomialFour N b f p x-p x =
      actualFlatSourceQuadraticFour N (f+fderiv ℝ p 0 b) x := by
    simp only [actualFlatDriftCorrectedPolynomialFour,Pi.add_apply,add_sub_cancel_left]
  rw [he]
  exact (actualFlatSourceQuadraticFour_value_bound hN _ x).trans
    (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (actual_flat_drift_correction_coefficient_bound_four hf hb p)
        (by norm_num)) (sq_nonneg _))

theorem actual_flat_drift_correction_hessian_bound_four {N b : E} (hN : ‖N‖=1)
    {f delta : ℝ} (hf : |f| ≤ delta) (hb : ‖b‖ ≤ delta)
    {p : E → ℝ} (hp : IsQuadraticPolynomial p) (x : E) :
    ‖realHessian (actualFlatDriftCorrectedPolynomialFour N b f p) x-realHessian p x‖ ≤
      delta*(1+‖fderiv ℝ p 0‖) := by
  have he : realHessian (actualFlatDriftCorrectedPolynomialFour N b f p) x-realHessian p x =
      realHessian (actualFlatSourceQuadraticFour N (f+fderiv ℝ p 0 b)) x := by
    rw [actual_flat_drift_corrected_hessian_four N b f hp,actualFlatSourceQuadraticFour_hessian]
    ext v w
    simp only [_root_.add_apply,_root_.sub_apply]
    ring
  rw [he,actualFlatSourceQuadraticFour_hessian_norm hN]
  exact actual_flat_drift_correction_coefficient_bound_four hf hb p

end PowerConvexity
