import PowerConvexity.Analysis.ActualFlatDriftIterationInputFour

/-! # Every scaled residual is the actual drift perturbation datum of one fixed PDE -/
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

theorem actual_flat_drift_input_frozen_four {N : E} (hN : ‖N‖=1)
    {lam Lambda alpha kappa : ℝ} (halpha : 0 < alpha)
    (D : ActualFlatDriftIterationInputFour N lam Lambda alpha kappa) : D.coeff.a 0=1 := by
  have h0 : (0 : E) ∈ closure (actualFlatUpperBallFour N 1) :=
    actual_flat_boundary_point_mem_closure_four hN (by simp) (by simp)
  have hr : Continuous (fun x : E => kappa*‖x‖^alpha) :=
    continuous_const.mul (continuous_norm.rpow_const (fun _ => Or.inr halpha.le))
  ext i j
  have hc : ContinuousOn (fun x => |D.coeff.a x i j-(1 : Mat) i j|)
      (closure (actualFlatUpperBallFour N 1)) :=
    (((D.continuous i j).sub continuousOn_const).abs).mono (actualFlatUpperBallFour_closure_subset N 1)
  have hh : |D.coeff.a 0 i j-(1 : Mat) i j| ≤ kappa*‖(0 : E)‖^alpha :=
    le_on_closure (fun x hx => (actual_matrix_difference_entry_bound_four _ _ i j).trans
      (D.growth x hx)) hc hr.continuousOn h0
  rw [norm_zero,Real.zero_rpow halpha.ne',mul_zero] at hh
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hh (abs_nonneg _)))

def actualFlatDriftResidualDataFour {N : E} {lam Lambda alpha kappa R a M G delta : ℝ}
    (halpha : 0 < alpha) (halpha1 : alpha ≤ 1) (hk : 0 ≤ kappa)
    (hR : 0 < R) (hR1 : R ≤ 1) (ha : 0 < a) (hRa : R^alpha ≤ a)
    (hM : 0 ≤ M) (hG : 0 ≤ G) (hsmall : kappa*(1+17*M+G) ≤ delta)
    (D : ActualFlatDriftIterationInputFour N lam Lambda alpha kappa)
    {q : E → ℝ} (hq : IsQuadraticPolynomial q)
    (hq0 : ∀ x : E, inner ℝ N x=0 → q x=0)
    (hH : ‖realHessian q 0‖ ≤ M) (hD : ‖fderiv ℝ q 0‖ ≤ G)
    (hfreeze : (realBlockHessian realDirections imagDirections q 0).trace+
      fderiv ℝ q 0 (D.drift 0) = -D.source 0)
    (herr : ∀ x ∈ actualFlatClosedUpperBallFour N R, |D.solution x-q x| ≤ a*R^2) :
    ActualFlatDriftPerturbationDataFour N lam Lambda delta := by
  have hkdelta : kappa ≤ delta :=
    (show kappa ≤ kappa*(1+17*M+G) by nlinarith [mul_nonneg hk hM,mul_nonneg hk hG]).trans hsmall
  have hsub : actualFlatUpperBallFour N 1 ⊆ actualFlatClosedUpperBallFour N 1 := by
    intro x hx
    exact ⟨ball_subset_closedBall hx.1,(show 0 < inner ℝ N x from hx.2).le⟩
  have hreg := actual_flat_residual_regularity_four (b := a) hR hR1 hq D.solution_regular
    D.solution_continuous D.solution_zero hq0
  have hbc : ContinuousOn (fun z : E => R • D.drift (R • z)) (actualFlatClosedUpperBallFour N 1) :=
    (D.drift_continuous.comp (by fun_prop) (actual_flat_closed_unit_dilation_maps_four N hR hR1)).const_smul R
  have hfc := actual_flat_drift_residual_continuous_four (a := a) hR hR1 D.continuous
    D.drift_continuous D.source_continuous hq
  exact {
    coeff := actualFlatDilationCoeffFour hR hR1 D.coeff
    drift := fun z => R • D.drift (R • z)
    source := actualFlatDriftResidualSourceFour D.coeff.a D.drift D.source q R a
    solution := normalizedScalarResidualTwo D.solution q R a
    lower := D.lower
    upper := D.upper
    positive := fun x hx => D.positive _ (actual_flat_unit_dilation_maps_four N hR hR1 hx)
    regular := actual_flat_dilation_coeff_regular_four hR hR1 D.coeff D.regular
    divergence := actual_flat_dilation_column_divergence_four hR hR1 D.coeff D.regular D.divergence
    near_identity := by
      intro x hx i j
      have hm := actual_flat_unit_dilation_maps_four N hR hR1 hx
      exact ((actual_matrix_difference_entry_bound_four _ _ i j).trans (D.growth _ hm)).trans
        ((mul_le_mul_of_nonneg_left (actual_flat_norm_rpow_le_one_four halpha.le hm) hk).trans
          (by simpa only [mul_one] using hkdelta))
    drift_continuous := hbc.mono hsub
    drift_bound := by
      intro x hx
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos hR]
      exact (mul_le_mul_of_nonneg_left (D.drift_bound _ (actual_flat_unit_dilation_maps_four N hR hR1 hx)) hR.le).trans
        ((mul_le_mul_of_nonneg_right hR1 hk).trans (by simpa only [one_mul] using hkdelta))
    source_continuous := hfc.mono hsub
    source_bound := actual_flat_drift_residual_small_four halpha halpha1 hk hR hR1 ha hRa
      hM hG hsmall D hq hH hD hfreeze
    solution_regular := hreg.1
    solution_continuous := hreg.2.1
    solution_zero := hreg.2.2
    solution_bound := actual_flat_residual_bound_four hR ha herr
    equation := fun x hx => actual_normalized_residual_drift_equation_four
      (actualFlatUpperBallFour_isOpen N 1) hR D.solution_regular hq D.equation x
      (actual_flat_unit_dilation_maps_four N hR hR1 hx)
  }

end PowerConvexity
