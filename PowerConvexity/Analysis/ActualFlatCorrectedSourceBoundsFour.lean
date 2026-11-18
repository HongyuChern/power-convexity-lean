import PowerConvexity.Analysis.ActualFlatSourceCorrectionFour

/-! # The actual corrected source retains quantitative Holder control -/
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

theorem actual_flat_corrected_source_holder_four {N : E} (hN : ‖N‖=1)
    {U : Set E} {A : E → Mat} {f : E → ℝ} {b Ka Kf alpha : ℝ}
    (hA : ∀ x ∈ U, ∀ y ∈ U,
      ‖actualMatrixOperatorTwo (A x)-actualMatrixOperatorTwo (A y)‖ ≤ Ka*‖x-y‖^alpha)
    (hf : ∀ x ∈ U, ∀ y ∈ U, |f x-f y| ≤ Kf*‖x-y‖^alpha) :
    ∀ x ∈ U, ∀ y ∈ U,
      |(f x-quadraticScalarSourceTwo A (actualFlatSourceQuadraticFour N b) x)-
        (f y-quadraticScalarSourceTwo A (actualFlatSourceQuadraticFour N b) y)| ≤
      (Kf+16*Ka*|b|)*‖x-y‖^alpha := by
  intro x hx y hy
  have hq := actual_quadratic_source_holder_four (actualFlatSourceQuadraticFour_quadratic N b)
    (abs_nonneg b) (actualFlatSourceQuadraticFour_hessian_norm hN b 0).le hA x hx y hy
  rw [show (f x-quadraticScalarSourceTwo A (actualFlatSourceQuadraticFour N b) x)-
      (f y-quadraticScalarSourceTwo A (actualFlatSourceQuadraticFour N b) y) =
      (f x-f y)-(quadraticScalarSourceTwo A (actualFlatSourceQuadraticFour N b) x-
        quadraticScalarSourceTwo A (actualFlatSourceQuadraticFour N b) y) by ring]
  exact (abs_sub _ _).trans ((add_le_add (hf x hx y hy) hq).trans_eq (by ring))

theorem actual_flat_corrected_source_growth_four {N : E} (hN : ‖N‖=1)
    {U : Set E} {A : E → Mat} {f : E → ℝ} {b Ka Kf alpha : ℝ}
    (hA : ∀ x ∈ U,
      ‖actualMatrixOperatorTwo (A x)-actualMatrixOperatorTwo (1 : Mat)‖ ≤ Ka*‖x‖^alpha)
    (hf : ∀ x ∈ U, |f x-b| ≤ Kf*‖x‖^alpha) :
    ∀ x ∈ U, |f x-quadraticScalarSourceTwo A (actualFlatSourceQuadraticFour N b) x| ≤
      (Kf+16*Ka*|b|)*‖x‖^alpha := by
  intro x hx
  have hh := actual_flat_constant_source_correction_error_four hN A b x
  have hq : |quadraticScalarSourceTwo A (actualFlatSourceQuadraticFour N b) x-b| ≤
      16*(Ka*‖x‖^alpha)*|b| := hh.trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hA x hx) (by norm_num)) (abs_nonneg b))
  rw [show f x-quadraticScalarSourceTwo A (actualFlatSourceQuadraticFour N b) x =
      (f x-b)-(quadraticScalarSourceTwo A (actualFlatSourceQuadraticFour N b) x-b) by ring]
  exact (abs_sub _ _).trans ((add_le_add (hf x hx) hq).trans_eq (by ring))

theorem actual_flat_scaled_corrected_source_holder_four {N : E} (hN : ‖N‖=1)
    {A : E → Mat} {f : E → ℝ} {b R a Ka Kf alpha : ℝ}
    (hR : 0 < R) (hR1 : R ≤ 1) (ha : 0 < a)
    (hA : ∀ x ∈ actualFlatUpperBallFour N 1, ∀ y ∈ actualFlatUpperBallFour N 1,
      ‖actualMatrixOperatorTwo (A x)-actualMatrixOperatorTwo (A y)‖ ≤ Ka*‖x-y‖^alpha)
    (hf : ∀ x ∈ actualFlatUpperBallFour N 1, ∀ y ∈ actualFlatUpperBallFour N 1,
      |f x-f y| ≤ Kf*‖x-y‖^alpha) :
    ∀ x ∈ actualFlatUpperBallFour N 1, ∀ y ∈ actualFlatUpperBallFour N 1,
      |actualFlatResidualSourceFour A f (actualFlatSourceQuadraticFour N b) R a x-
        actualFlatResidualSourceFour A f (actualFlatSourceQuadraticFour N b) R a y| ≤
      (a⁻¹*R^alpha*(Kf+16*Ka*|b|))*‖x-y‖^alpha :=
  actual_flat_residual_source_holder_four (actualFlatSourceQuadraticFour_quadratic N b)
    hR hR1 ha (abs_nonneg b) (actualFlatSourceQuadraticFour_hessian_norm hN b 0).le hA hf

theorem actual_flat_scaled_corrected_source_growth_four {N : E} (hN : ‖N‖=1)
    {A : E → Mat} {f : E → ℝ} {b R a Ka Kf alpha : ℝ}
    (hR : 0 < R) (hR1 : R ≤ 1) (ha : 0 < a)
    (hA : ∀ x ∈ actualFlatUpperBallFour N 1,
      ‖actualMatrixOperatorTwo (A x)-actualMatrixOperatorTwo (1 : Mat)‖ ≤ Ka*‖x‖^alpha)
    (hf : ∀ x ∈ actualFlatUpperBallFour N 1, |f x-b| ≤ Kf*‖x‖^alpha) :
    ∀ x ∈ actualFlatUpperBallFour N 1,
      |actualFlatResidualSourceFour A f (actualFlatSourceQuadraticFour N b) R a x| ≤
      (a⁻¹*R^alpha*(Kf+16*Ka*|b|))*‖x‖^alpha := by
  intro x hx
  have hh := actual_flat_corrected_source_growth_four hN hA hf _
    (actual_flat_unit_dilation_maps_four N hR hR1 hx)
  simp only [actualFlatResidualSourceFour,abs_mul,abs_of_pos (inv_pos.mpr ha)]
  apply (mul_le_mul_of_nonneg_left hh (inv_pos.mpr ha).le).trans_eq
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos hR,Real.mul_rpow hR.le (norm_nonneg x)]
  ring

end PowerConvexity
