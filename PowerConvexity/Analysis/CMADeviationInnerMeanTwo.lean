import PowerConvexity.Analysis.CMADeviationMeanTwo
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! # The mean estimate on the actual inner ball.
The radius and Jacobian are explicit: scaling by one half in real
dimension four contributes 16. All data are needed only in the unit ball.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology BigOperators ComplexOrder Pointwise
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)

theorem actual_shifted_CMA_upper_deficit_inner_mean_two
    {w : E → ℝ} (hw : ContDiffOn ℝ 2 w (ball 0 1))
    (hpsh : ∀ x ∈ ball 0 1, (1+complexHessian realDirections imagDirections w x).PosSemidef)
    (hdet : ∀ x ∈ ball 0 1, (1+complexHessian realDirections imagDirections w x).det = 1)
    (b : ℝ) (hupper : ∀ x ∈ ball 0 1, w x ≤ b)
    {y : E} (hy : y ∈ ball (0 : E) (1/8 : ℝ)) :
    (∫ x in ball (0 : E) (1/8 : ℝ), b-w x) ≤
      weakHarnackMeanConstant (2+2) (by norm_num) 1 * (b-w y) := by
  have hy' : y ∈ ball (0 : E) ((1/2 : ℝ)/4) := by
    simpa only [show (1/2 : ℝ)/4 = 1/8 by norm_num] using hy
  have hh := actual_shifted_CMA_upper_deficit_rescaled_mean_two (w := w) isOpen_ball hw hpsh hdet
    (x₀ := (0 : E)) (r := (1/2 : ℝ)) (R := (3/4 : ℝ)) (by norm_num) (by norm_num)
    (closedBall_subset_ball (by norm_num : (3/4 : ℝ) < 1)) b
    (fun x hx => hupper x ((ball_subset_ball (by norm_num : (1/2 : ℝ) ≤ 1)) hx))
    (y := y) hy'
  simp only [zero_add] at hh
  have hs := Measure.setIntegral_comp_smul_of_pos volume (fun x : E => b-w x)
    (ball (0 : E) (1/4 : ℝ)) (by norm_num : (0 : ℝ) < 1/2)
  have hfin : Module.finrank ℝ E = 4 := by simp [AmbientSpace]
  rw [hfin,_root_.smul_ball (by norm_num : (1/2 : ℝ) ≠ 0),smul_zero] at hs
  norm_num only [Real.norm_eq_abs,abs_of_pos (by norm_num : (0 : ℝ) < 1/2),
    show (1/2 : ℝ)*(1/4) = 1/8 by norm_num,
    show ((1/2 : ℝ)^4)⁻¹ = 16 by norm_num,smul_eq_mul] at hs
  rw [hs] at hh
  have hi : 0 ≤ ∫ x in ball (0 : E) (1/8 : ℝ), b-w x := by
    apply setIntegral_nonneg measurableSet_ball
    intro x hx
    exact sub_nonneg.mpr (hupper x ((ball_subset_ball (by norm_num : (1/8 : ℝ) ≤ 1)) hx))
  linarith only [hh,hi]

end PowerConvexity
