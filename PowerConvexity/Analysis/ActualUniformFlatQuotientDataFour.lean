import PowerConvexity.Analysis.ActualUniformFlatSlopeImprovementFour
import PowerConvexity.Analysis.ActualFlatDriftPhysicalNormalizationFour

/-! # Actual rough-coefficient equation and boundary-quotient dilation

This data contains only the same real equation, actual regularity and bounded
drift/source needed by the quotient argument. Its dilation has coefficient
a(r*x), drift r*b(r*x), source r*f(r*x) and response u(r*x)/r.
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

structure ActualFlatQuotientEquationFour (N : E) (Lambda B F : ℝ) where
  coeff : NormalizedEllipticCoeff (2+2) (actualFlatUpperBallFour N 1)
  upper : coeff.1.Λ ≤ Lambda
  regular : ∀ i j, ContDiffOn ℝ 1 (fun x => coeff.1.a x i j) (actualFlatUpperBallFour N 1)
  positive : ∀ x ∈ actualFlatUpperBallFour N 1, (coeff.1.a x).PosDef
  drift : E → E
  drift_continuous : ContinuousOn drift (actualFlatUpperBallFour N 1)
  divergence : ∀ x ∈ actualFlatUpperBallFour N 1,
    actualCoefficientColumnDivergenceFour coeff.1.a x=drift x
  drift_bound : ∀ x ∈ actualFlatUpperBallFour N 1, ‖drift x‖ ≤ B
  source : E → ℝ
  source_continuous : ContinuousOn source (actualFlatUpperBallFour N 1)
  source_bound : ∀ x ∈ actualFlatUpperBallFour N 1, |source x| ≤ F
  solution : E → ℝ
  solution_regular : ContDiffOn ℝ 2 solution (actualFlatUpperBallFour N 1)
  solution_continuous : ContinuousOn solution (actualFlatClosedUpperBallFour N 1)
  equation : ∀ x ∈ actualFlatUpperBallFour N 1,
    (∑ i, ∑ j, coeff.1.a x i j*euclideanHessian solution x i j)+
      fderiv ℝ solution x (drift x) = -source x

def actualFlatQuotientDilateFour {N : E} {Lambda B F r : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (D : ActualFlatQuotientEquationFour N Lambda B F) :
    ActualFlatQuotientEquationFour N Lambda (r*B) (r*F) := by
  let A : NormalizedEllipticCoeff (2+2) (actualFlatUpperBallFour N 1) :=
    ⟨actualFlatDilationCoeffFour hr hr1 D.coeff.1,D.coeff.property⟩
  have hmap := actual_flat_unit_dilation_maps_four N hr hr1
  have hmapC := actual_flat_closed_unit_dilation_maps_four N hr hr1
  refine {
    coeff := A
    upper := D.upper
    regular := actual_flat_dilation_coeff_regular_four hr hr1 D.coeff.1 D.regular
    positive := fun x hx => D.positive _ (hmap hx)
    drift := fun x => r • D.drift (r • x)
    drift_continuous := (D.drift_continuous.comp (by fun_prop) hmap).const_smul r
    divergence := actual_flat_dilation_column_divergence_four hr hr1 D.coeff.1 D.regular D.divergence
    drift_bound := ?_
    source := fun x => r*D.source (r • x)
    source_continuous := continuousOn_const.mul (D.source_continuous.comp (by fun_prop) hmap)
    source_bound := ?_
    solution := fun x => r⁻¹*D.solution (r • x)
    solution_regular := contDiffOn_const.mul (D.solution_regular.comp (contDiffOn_id.const_smul r) hmap)
    solution_continuous := continuousOn_const.mul (D.solution_continuous.comp (by fun_prop) hmapC)
    equation := ?_
  }
  · intro x hx
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr]
    exact mul_le_mul_of_nonneg_left (D.drift_bound _ (hmap hx)) hr.le
  · intro x hx
    rw [abs_mul,abs_of_pos hr]
    exact mul_le_mul_of_nonneg_left (D.source_bound _ (hmap hx)) hr.le
  · intro x hx
    have hq : IsQuadraticPolynomial (fun _ : E => (0 : ℝ)) := (quadraticSubmodule E).zero_mem
    have he : normalizedScalarResidualTwo D.solution (fun _ => 0) r r⁻¹=
        (fun y => r⁻¹*D.solution (r • y)) := by
      funext y
      dsimp only [normalizedScalarResidualTwo]
      simp only [sub_zero]
      field_simp
    have hh := actual_normalized_residual_drift_equation_four
      (actualFlatUpperBallFour_isOpen N 1) (a := r⁻¹) hr D.solution_regular hq D.equation x (hmap hx)
    rw [he,actual_flat_drift_zero_residual_source_four,inv_inv] at hh
    exact hh

theorem actual_flat_quotient_dilate_solution_four {N : E} {Lambda B F r : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (D : ActualFlatQuotientEquationFour N Lambda B F) (x : E) :
    (actualFlatQuotientDilateFour hr hr1 D).solution x=r⁻¹*D.solution (r • x) := rfl

theorem actual_flat_quotient_slope_step_four {Lambda : ℝ} (hLambda : 1 ≤ Lambda) :
    ∃ delta > 0, delta ≤ (1/32 : ℝ) ∧ ∃ K > 0,
      ∀ N : E, ‖N‖=1 → ∀ B ≥ 0, B ≤ 1/2 → ∀ F > 0,
      ∀ D : ActualFlatQuotientEquationFour N Lambda B F,
      ∀ lo hi S : ℝ, lo ≤ hi → 0 ≤ S → |lo| ≤ S → |hi| ≤ S →
      (∀ x ∈ actualFlatClosedUpperBallFour N 1,
        lo*inner ℝ N x ≤ D.solution x ∧ D.solution x ≤ hi*inner ℝ N x) →
      ∃ lo' hi' : ℝ, lo ≤ lo' ∧ lo' ≤ hi' ∧ hi' ≤ hi ∧
        hi'-lo' ≤ (1-delta)*(hi-lo)+K*(F+B*S) ∧
        ∀ x ∈ actualFlatClosedUpperBallFour N (1/64),
          lo'*inner ℝ N x ≤ D.solution x ∧ D.solution x ≤ hi'*inner ℝ N x := by
  obtain ⟨delta,hd,hdb,K,hK,hstep⟩ := actual_uniform_flat_slope_improvement_four hLambda
  refine ⟨delta,hd,hdb,K,hK,?_⟩
  intro N hN B hB hBsmall F hF D
  exact hstep N hN D.coeff D.upper D.regular D.positive D.drift D.drift_continuous
    D.divergence B hB hBsmall D.drift_bound D.source D.solution D.source_continuous
    D.solution_regular D.solution_continuous F hF D.source_bound D.equation

end PowerConvexity
