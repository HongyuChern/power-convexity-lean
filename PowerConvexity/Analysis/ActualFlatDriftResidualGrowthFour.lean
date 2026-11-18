import PowerConvexity.Analysis.ActualFlatDriftResidualEquationFour
import PowerConvexity.Analysis.ActualFlatFrozenEquationFour

/-! # Quantitative growth of the full residual from its actual frozen equation -/
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

theorem actual_quadratic_drift_difference_four {q : E → ℝ} (hq : IsQuadraticPolynomial q)
    (b : E → E) (x : E) :
    fderiv ℝ q x (b x)-fderiv ℝ q 0 (b 0) =
      fderiv ℝ q 0 (b x-b 0)+realHessian q 0 x (b x) := by
  rw [quadratic_fderiv_from_jet_zero hq x]
  simp only [_root_.add_apply,map_sub]
  ring

theorem actual_quadratic_drift_difference_bound_four {q : E → ℝ} (hq : IsQuadraticPolynomial q)
    (b : E → E) (x : E) :
    |fderiv ℝ q x (b x)-fderiv ℝ q 0 (b 0)| ≤
      ‖fderiv ℝ q 0‖*‖b x-b 0‖+‖realHessian q 0‖*‖x‖*‖b x‖ := by
  rw [actual_quadratic_drift_difference_four hq]
  have ht : |fderiv ℝ q 0 (b x-b 0)+realHessian q 0 x (b x)| ≤
      |fderiv ℝ q 0 (b x-b 0)|+|realHessian q 0 x (b x)| := by
    simpa only [Real.norm_eq_abs] using
      (norm_add_le (fderiv ℝ q 0 (b x-b 0)) (realHessian q 0 x (b x)))
  exact ht.trans
    (add_le_add ((fderiv ℝ q 0).le_opNorm _) ((realHessian q 0).le_opNorm₂ _ _))

theorem actual_full_frozen_residual_zero_four {q : E → ℝ} {b0 : E} {f0 : ℝ}
    (hfreeze : (realBlockHessian realDirections imagDirections q 0).trace+
      fderiv ℝ q 0 b0 = -f0) :
    f0-quadraticScalarSourceTwo (fun _ => (1 : Mat)) q 0+fderiv ℝ q 0 b0=0 := by
  rw [actual_quadratic_source_identity_trace_four]
  linarith

theorem actual_full_drift_residual_bound_four (A : E → Mat) (b : E → E) (f : E → ℝ)
    {q : E → ℝ} (hq : IsQuadraticPolynomial q)
    (hfreeze : (realBlockHessian realDirections imagDirections q 0).trace+
      fderiv ℝ q 0 (b 0) = -f 0) (x : E) :
    |f x-quadraticScalarSourceTwo A q x+fderiv ℝ q x (b x)| ≤
      |f x-f 0|+16*‖actualMatrixOperatorTwo (A x)-actualMatrixOperatorTwo (1 : Mat)‖*‖realHessian q 0‖+
      (‖fderiv ℝ q 0‖*‖b x-b 0‖+‖realHessian q 0‖*‖x‖*‖b x‖) := by
  have h0 := actual_full_frozen_residual_zero_four hfreeze
  have he : f x-quadraticScalarSourceTwo A q x+fderiv ℝ q x (b x) =
      ((f x-f 0)-(quadraticScalarSourceTwo A q x-
        quadraticScalarSourceTwo (fun _ => (1 : Mat)) q 0))+
      (fderiv ℝ q x (b x)-fderiv ℝ q 0 (b 0)) := by linarith
  rw [he]
  have ht : |((f x-f 0)-(quadraticScalarSourceTwo A q x-
      quadraticScalarSourceTwo (fun _ => (1 : Mat)) q 0))+
      (fderiv ℝ q x (b x)-fderiv ℝ q 0 (b 0))| ≤
      |(f x-f 0)-(quadraticScalarSourceTwo A q x-
        quadraticScalarSourceTwo (fun _ => (1 : Mat)) q 0)|+
      |fderiv ℝ q x (b x)-fderiv ℝ q 0 (b 0)| := by
    simpa only [Real.norm_eq_abs] using (norm_add_le
        ((f x-f 0)-(quadraticScalarSourceTwo A q x-quadraticScalarSourceTwo (fun _ => (1 : Mat)) q 0))
        (fderiv ℝ q x (b x)-fderiv ℝ q 0 (b 0)))
  apply ht.trans
  apply add_le_add _ (actual_quadratic_drift_difference_bound_four hq b x)
  exact (abs_sub _ _).trans (add_le_add (le_refl _) (actual_quadratic_source_difference_bound_four
    hq (norm_nonneg (realHessian q 0)) le_rfl (A x) 1 x 0))

theorem actual_full_drift_residual_holder_growth_four
    {U : Set E} (A : E → Mat) (b : E → E) (f : E → ℝ)
    {q : E → ℝ} (hq : IsQuadraticPolynomial q) {Ka Kb Kf B M G alpha : ℝ}
    (hKa : 0 ≤ Ka) (hKb : 0 ≤ Kb) (hB : 0 ≤ B) (hM : 0 ≤ M) (hG : 0 ≤ G)
    (hH : ‖realHessian q 0‖ ≤ M) (hD : ‖fderiv ℝ q 0‖ ≤ G)
    (hfreeze : (realBlockHessian realDirections imagDirections q 0).trace+
      fderiv ℝ q 0 (b 0) = -f 0)
    (hA : ∀ x ∈ U, ‖actualMatrixOperatorTwo (A x)-actualMatrixOperatorTwo (1 : Mat)‖ ≤ Ka*‖x‖^alpha)
    (hb : ∀ x ∈ U, ‖b x-b 0‖ ≤ Kb*‖x‖^alpha)
    (hbn : ∀ x ∈ U, ‖b x‖ ≤ B)
    (hf : ∀ x ∈ U, |f x-f 0| ≤ Kf*‖x‖^alpha) :
    ∀ x ∈ U, |f x-quadraticScalarSourceTwo A q x+fderiv ℝ q x (b x)| ≤
      (Kf+16*Ka*M+G*Kb)*‖x‖^alpha+M*B*‖x‖ := by
  intro x hx
  apply (actual_full_drift_residual_bound_four A b f hq hfreeze x).trans
  have hp : 0 ≤ ‖x‖^alpha := Real.rpow_nonneg (norm_nonneg _) _
  have h1 : 16*‖actualMatrixOperatorTwo (A x)-actualMatrixOperatorTwo (1 : Mat)‖*‖realHessian q 0‖ ≤
      (16*Ka*‖x‖^alpha)*M :=
    mul_le_mul (by nlinarith [hA x hx]) hH (norm_nonneg (realHessian q 0)) (by positivity)
  have h2 : ‖fderiv ℝ q 0‖*‖b x-b 0‖ ≤ G*(Kb*‖x‖^alpha) :=
    mul_le_mul hD (hb x hx) (norm_nonneg _) hG
  have h3 : ‖realHessian q 0‖*‖x‖*‖b x‖ ≤ M*‖x‖*B :=
    mul_le_mul (mul_le_mul_of_nonneg_right hH (norm_nonneg _)) (hbn x hx)
      (norm_nonneg _) (mul_nonneg hM (norm_nonneg _))
  exact (add_le_add (add_le_add (hf x hx) h1) (add_le_add h2 h3)).trans_eq (by ring)

end PowerConvexity
