import PowerConvexity.Analysis.CMADeviationInnerMeanTwo

/-! # Actual low-level volume gives a pointwise upper deficit.
Open and closed inner balls are compared using Haar sphere-nullness.
All integrals and level sets refer to the original solution.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology BigOperators ComplexOrder ENNReal
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)

theorem actual_shifted_CMA_lowset_forces_deficit_two
    {w : E → ℝ} (hw : ContDiffOn ℝ 2 w (ball 0 1))
    (hpsh : ∀ x ∈ ball 0 1, (1+complexHessian realDirections imagDirections w x).PosSemidef)
    (hdet : ∀ x ∈ ball 0 1, (1+complexHessian realDirections imagDirections w x).det = 1)
    (b : ℝ) (hupper : ∀ x ∈ ball 0 1, w x ≤ b)
    {S : Set E} (hS : MeasurableSet S) (hsub : S ⊆ closedBall 0 (1/8 : ℝ))
    (d : ℝ) (hlow : ∀ x ∈ S, w x ≤ b-d)
    {y : E} (hy : y ∈ ball (0 : E) (1/8 : ℝ)) :
    d*volume.real S ≤ weakHarnackMeanConstant (2+2) (by norm_num) 1 * (b-w y) := by
  have hU : closedBall (0 : E) (1/8 : ℝ) ⊆ ball 0 1 :=
    closedBall_subset_ball (by norm_num)
  have hint : IntegrableOn (fun x => b-w x) (closedBall (0 : E) (1/8 : ℝ)) volume :=
    ContinuousOn.integrableOn_compact (isCompact_closedBall _ _)
      (continuousOn_const.sub (hw.continuousOn.mono hU))
  have hfinite : volume (closedBall (0 : E) (1/8 : ℝ)) ≠ (⊤ : ℝ≥0∞) :=
    (isCompact_closedBall _ _).measure_lt_top.ne
  have hlo : d*volume.real S ≤ ∫ x in S, b-w x :=
    setIntegral_ge_of_const_le_real hS (measure_ne_top_of_subset hsub hfinite)
      (fun x hx => by linarith only [hlow x hx]) (hint.mono_set hsub)
  have hmono : (∫ x in S, b-w x) ≤ ∫ x in closedBall (0 : E) (1/8 : ℝ), b-w x := by
    apply setIntegral_mono_set hint _ hsub.eventuallyLE
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
    exact sub_nonneg.mpr (hupper x (hU hx))
  have hae : ball (0 : E) (1/8 : ℝ) =ᵐ[volume] closedBall 0 (1/8 : ℝ) :=
    ae_eq_of_subset_of_measure_ge ball_subset_closedBall
      (Measure.addHaar_closedBall_eq_addHaar_ball volume _ _).le
      measurableSet_ball.nullMeasurableSet hfinite
  have heq : (∫ x in closedBall (0 : E) (1/8 : ℝ), b-w x) =
      ∫ x in ball (0 : E) (1/8 : ℝ), b-w x := setIntegral_congr_set hae.symm
  exact hlo.trans (hmono.trans (heq.le.trans
    (actual_shifted_CMA_upper_deficit_inner_mean_two hw hpsh hdet b hupper hy)))

theorem actual_shifted_CMA_half_level_forces_deficit_two
    {w : E → ℝ} (hw : ContDiffOn ℝ 2 w (ball 0 1))
    (hpsh : ∀ x ∈ ball 0 1, (1+complexHessian realDirections imagDirections w x).PosSemidef)
    (hdet : ∀ x ∈ ball 0 1, (1+complexHessian realDirections imagDirections w x).det = 1)
    {b : ℝ} (hb : 0 ≤ b) (hupper : ∀ x ∈ ball 0 1, w x ≤ b)
    (hlevel : volume.real {x | x ∈ closedBall (0 : E) (1/8 : ℝ) ∧ b/2 < w x} ≤
      volume.real (closedBall (0 : E) (1/8 : ℝ))/2)
    {y : E} (hy : y ∈ ball (0 : E) (1/8 : ℝ)) :
    (b/4)*volume.real (closedBall (0 : E) (1/8 : ℝ)) ≤
      weakHarnackMeanConstant (2+2) (by norm_num) 1 * (b-w y) := by
  let S : Set E := {x | x ∈ closedBall (0 : E) (1/8 : ℝ) ∧ w x ≤ b/2}
  have hU : closedBall (0 : E) (1/8 : ℝ) ⊆ ball 0 1 := closedBall_subset_ball (by norm_num)
  have hS : MeasurableSet S := (isClosed_closedBall.isClosed_le
    (hw.continuousOn.mono hU) continuousOn_const).measurableSet
  have hsub : S ⊆ closedBall (0 : E) (1/8 : ℝ) := fun _ hx => hx.1
  have hdiff : closedBall (0 : E) (1/8 : ℝ) \ S =
      {x | x ∈ closedBall (0 : E) (1/8 : ℝ) ∧ b/2 < w x} := by
    ext x
    simp only [Set.mem_sdiff,mem_setOf_eq,S,not_and,not_le]
    tauto
  have hfinite : volume (closedBall (0 : E) (1/8 : ℝ)) ≠ (⊤ : ℝ≥0∞) :=
    (isCompact_closedBall _ _).measure_lt_top.ne
  have hmeasure := measureReal_sdiff (μ := volume) hsub hS hfinite
  rw [hdiff] at hmeasure
  have hmass : volume.real (closedBall (0 : E) (1/8 : ℝ))/2 ≤ volume.real S := by
    linarith only [hlevel,hmeasure]
  have hh := actual_shifted_CMA_lowset_forces_deficit_two hw hpsh hdet b hupper hS hsub
    (b/2) (fun x hx => by have hv := hx.2; linarith only [hv]) hy
  have hmul := mul_le_mul_of_nonneg_left hmass (by positivity : 0 ≤ b/2)
  nlinarith only [hh,hmul]

end PowerConvexity
