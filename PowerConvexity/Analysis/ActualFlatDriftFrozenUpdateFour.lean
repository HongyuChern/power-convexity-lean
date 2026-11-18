import PowerConvexity.Analysis.ActualFlatDriftResidualGrowthFour
import PowerConvexity.Analysis.ActualFlatIterationStepFour

/-! # Weighted actual polynomial updates preserve the full frozen drift equation -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
local notation "Mat" => Matrix (Fin (2+2)) (Fin (2+2)) ℝ
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_flat_drift_residual_source_zero_four {A : E → Mat} {b : E → E}
    {f q : E → ℝ} (hA : A 0=1)
    (hfreeze : (realBlockHessian realDirections imagDirections q 0).trace+
      fderiv ℝ q 0 (b 0) = -f 0) (R a : ℝ) :
    actualFlatDriftResidualSourceFour A b f q R a 0=0 := by
  have hs : quadraticScalarSourceTwo A q 0=quadraticScalarSourceTwo (fun _ => (1 : Mat)) q 0 := by
    simp only [quadraticScalarSourceTwo,hA]
  simp only [actualFlatDriftResidualSourceFour,smul_zero,hs,
    actual_full_frozen_residual_zero_four hfreeze,mul_zero]

theorem actual_flat_drift_quadratic_update_frozen_four {q p : E → ℝ}
    (hq : IsQuadraticPolynomial q) (hp : IsQuadraticPolynomial p)
    {R a : ℝ} (hR : 0 < R) (b0 : E) (f0 : ℝ)
    (hqt : (realBlockHessian realDirections imagDirections q 0).trace+fderiv ℝ q 0 b0 = -f0)
    (hpt : (realBlockHessian realDirections imagDirections p 0).trace+fderiv ℝ p 0 (R • b0) = 0) :
    (realBlockHessian realDirections imagDirections (scalarQuadraticUpdateTwo q p R a) 0).trace+
      fderiv ℝ (scalarQuadraticUpdateTwo q p R a) 0 b0 = -f0 := by
  have hd := congrArg (fun L : E →L[ℝ] ℝ => L b0)
    (scalarQuadraticUpdateTwo_jet_increments (a := a) hq hp hR).2.1
  simp only [_root_.sub_apply,_root_.smul_apply,smul_eq_mul] at hd
  have ht := actual_quadratic_update_trace_four (a := a) hq hp hR (0 : E)
  rw [smul_zero] at ht
  rw [map_smul,smul_eq_mul] at hpt
  rw [ht]
  linear_combination hqt + hd + a * hpt

theorem actual_flat_drift_quadratic_update_gradient_bound_four {q p : E → ℝ}
    (hq : IsQuadraticPolynomial q) (hp : IsQuadraticPolynomial p)
    {R a K : ℝ} (hR : 0 < R) (hR1 : R ≤ 1) (ha : 0 < a)
    (hK : 0 ≤ K) (hqD : ‖fderiv ℝ q 0‖ ≤ 2*K*(1-a))
    (hpD : ‖fderiv ℝ p 0‖ ≤ K) :
    ‖fderiv ℝ (scalarQuadraticUpdateTwo q p R a) 0‖ ≤ 2*K*(1-a/2) := by
  have he : fderiv ℝ (scalarQuadraticUpdateTwo q p R a) 0 =
      (fderiv ℝ (scalarQuadraticUpdateTwo q p R a) 0-fderiv ℝ q 0)+fderiv ℝ q 0 := by abel
  rw [he]
  apply (norm_add_le
    (fderiv ℝ (scalarQuadraticUpdateTwo q p R a) 0-fderiv ℝ q 0) (fderiv ℝ q 0)).trans
  rw [(scalarQuadraticUpdateTwo_jet_increments hq hp hR).2.1,norm_smul,
    Real.norm_eq_abs,abs_of_pos (mul_pos ha hR)]
  have hh : (a*R)*‖fderiv ℝ p 0‖ ≤ a*K := by
    calc
      _ ≤ (a*R)*K := mul_le_mul_of_nonneg_left hpD (mul_pos ha hR).le
      _ ≤ a*K := by nlinarith [mul_nonneg ha.le hK,mul_le_mul_of_nonneg_right hR1 (mul_nonneg ha.le hK)]
  nlinarith

end PowerConvexity
