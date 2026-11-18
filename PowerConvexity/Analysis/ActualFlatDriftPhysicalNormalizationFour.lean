import PowerConvexity.Analysis.ActualFlatDriftPhysicalInputFour

/-! # A genuine physical dilation of the coefficient, drift, density and solution -/
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

theorem actual_zero_quadratic_scalar_source_four (A : E → Mat) (x : E) :
    quadraticScalarSourceTwo A (fun _ => 0) x=0 := by
  have hh : realHessian (fun _ : E => (0 : ℝ)) x=0 := by unfold realHessian; simp
  simp only [quadraticScalarSourceTwo,euclideanHessian,hh,_root_.zero_apply,mul_zero,
    Finset.sum_const_zero,neg_zero]

theorem actual_flat_drift_zero_residual_source_four (A : E → Mat) (b : E → E)
    (f : E → ℝ) (R a : ℝ) (x : E) :
    actualFlatDriftResidualSourceFour A b f (fun _ => 0) R a x = a⁻¹*f (R • x) := by
  have hd : fderiv ℝ (fun _ : E => (0 : ℝ)) (R • x)=0 := by simp
  simp only [actualFlatDriftResidualSourceFour,actual_zero_quadratic_scalar_source_four,
    hd,_root_.zero_apply,sub_zero,add_zero]

def actualFlatDriftPhysicalNormalizeFour {N : E}
    {lam Lambda alpha Ka Kb Kf Bd B kappa R a : ℝ}
    (hR : 0 < R) (hR1 : R ≤ 1) (ha : 0 < a) (hKb : 0 ≤ Kb)
    (D : ActualFlatDriftPhysicalInputFour N lam Lambda alpha Ka Kb Kf Bd B)
    (hcoeff : Ka*R^alpha ≤ kappa) (hbholder : Kb*R^alpha ≤ kappa)
    (hbd : R*Bd ≤ kappa) (hsource : a⁻¹*Kf*R^alpha ≤ kappa) (hsize : B ≤ a*R^2) :
    ActualFlatDriftIterationInputFour N lam Lambda alpha kappa := by
  have hq : IsQuadraticPolynomial (fun _ : E => (0 : ℝ)) := (quadraticSubmodule E).zero_mem
  have hq0 (x : E) (_hx : inner ℝ N x=0) : (0 : ℝ)=0 := rfl
  have hreg := actual_flat_residual_regularity_four (b := a) hR hR1 hq
    D.solution_regular D.solution_continuous D.solution_zero hq0
  have herr : ∀ x ∈ actualFlatClosedUpperBallFour N R, |D.solution x-0| ≤ a*R^2 := by
    intro x hx
    rw [sub_zero]
    exact (D.solution_bound x ⟨closedBall_subset_closedBall hR1 hx.1,hx.2⟩).trans hsize
  have hfc : ContinuousOn
      (actualFlatDriftResidualSourceFour D.coeff.a D.drift D.source (fun _ => 0) R a)
      (actualFlatClosedUpperBallFour N 1) :=
    actual_flat_drift_residual_continuous_four hR hR1 D.continuous D.drift_continuous D.source_continuous hq
  exact {
    coeff := actualFlatDilationCoeffFour hR hR1 D.coeff
    drift := fun z => R • D.drift (R • z)
    source := actualFlatDriftResidualSourceFour D.coeff.a D.drift D.source (fun _ => 0) R a
    solution := normalizedScalarResidualTwo D.solution (fun _ => 0) R a
    lower := D.lower
    upper := D.upper
    positive := fun x hx => D.positive _ (actual_flat_unit_dilation_maps_four N hR hR1 hx)
    regular := actual_flat_dilation_coeff_regular_four hR hR1 D.coeff D.regular
    continuous := fun i j => (D.continuous i j).comp (by fun_prop)
      (actual_flat_closed_unit_dilation_maps_four N hR hR1)
    divergence := actual_flat_dilation_column_divergence_four hR hR1 D.coeff D.regular D.divergence
    growth := by
      intro x hx
      have hh := D.growth _ (actual_flat_unit_dilation_maps_four N hR hR1 hx)
      have he : Ka*‖R • x‖^alpha = (Ka*R^alpha)*‖x‖^alpha := by
        rw [norm_smul,Real.norm_eq_abs,abs_of_pos hR,Real.mul_rpow hR.le (norm_nonneg x)]
        ring
      rw [he] at hh
      exact hh.trans (mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg (norm_nonneg _) alpha))
    drift_continuous :=
      (D.drift_continuous.comp (by fun_prop) (actual_flat_closed_unit_dilation_maps_four N hR hR1)).const_smul R
    drift_bound := by
      intro x hx
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos hR]
      exact (mul_le_mul_of_nonneg_left (D.drift_bound _ (actual_flat_unit_dilation_maps_four N hR hR1 hx)) hR.le).trans hbd
    drift_growth := by
      intro x hx
      rw [smul_zero,← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos hR]
      have hh := mul_le_mul_of_nonneg_left
        (D.drift_growth _ (actual_flat_unit_dilation_maps_four N hR hR1 hx)) hR.le
      have he : R*(Kb*‖R • x‖^alpha) = (R*(Kb*R^alpha))*‖x‖^alpha := by
        rw [norm_smul,Real.norm_eq_abs,abs_of_pos hR,Real.mul_rpow hR.le (norm_nonneg x)]
        ring
      rw [he] at hh
      have hc : R*(Kb*R^alpha) ≤ kappa :=
        (mul_le_mul_of_nonneg_right hR1 (mul_nonneg hKb (Real.rpow_nonneg hR.le alpha))).trans
          (by simpa only [one_mul] using hbholder)
      exact hh.trans (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (norm_nonneg _) alpha))
    source_continuous := hfc
    source_growth := by
      intro x hx
      simp only [actual_flat_drift_zero_residual_source_four,smul_zero,← mul_sub,
        abs_mul,abs_of_pos (inv_pos.mpr ha)]
      have hh := mul_le_mul_of_nonneg_left
        (D.source_growth _ (actual_flat_unit_dilation_maps_four N hR hR1 hx)) (inv_pos.mpr ha).le
      have he : a⁻¹*(Kf*‖R • x‖^alpha) = (a⁻¹*Kf*R^alpha)*‖x‖^alpha := by
        rw [norm_smul,Real.norm_eq_abs,abs_of_pos hR,Real.mul_rpow hR.le (norm_nonneg x)]
        ring
      rw [he] at hh
      exact hh.trans (mul_le_mul_of_nonneg_right hsource (Real.rpow_nonneg (norm_nonneg _) alpha))
    solution_regular := hreg.1
    solution_continuous := hreg.2.1
    solution_zero := hreg.2.2
    solution_bound := actual_flat_residual_bound_four hR ha herr
    equation := fun x hx => actual_normalized_residual_drift_equation_four
      (actualFlatUpperBallFour_isOpen N 1) hR D.solution_regular hq D.equation x
      (actual_flat_unit_dilation_maps_four N hR hR1 hx)
  }

end PowerConvexity
