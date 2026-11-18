import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # A smooth convex primitive for an exact regularized maximum

This function is constant on the negative half-line and affine above one.
Its first derivative is between zero and one; its second derivative is
nonnegative. These are the precise signs needed to preserve the Levi form.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set MeasureTheory
open scoped ContDiff Topology
namespace PowerConvexity

noncomputable def smoothPositivePrimitive (x : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..x, Real.smoothTransition s

theorem smoothPositivePrimitive_hasDerivAt (x : ℝ) :
    HasDerivAt smoothPositivePrimitive (Real.smoothTransition x) x :=
  intervalIntegral.integral_hasDerivAt_right
    (Real.smoothTransition.continuous.intervalIntegrable _ _)
    Real.smoothTransition.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
    Real.smoothTransition.continuous.continuousAt

theorem smoothPositivePrimitive_deriv :
    deriv smoothPositivePrimitive = Real.smoothTransition :=
  funext fun x => (smoothPositivePrimitive_hasDerivAt x).deriv

theorem smoothPositivePrimitive_contDiff : ContDiff ℝ ∞ smoothPositivePrimitive := by
  apply contDiff_infty_iff_deriv.mpr
  exact ⟨fun x => (smoothPositivePrimitive_hasDerivAt x).differentiableAt,
    by rw [smoothPositivePrimitive_deriv]; exact Real.smoothTransition.contDiff⟩

theorem smoothPositivePrimitive_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    smoothPositivePrimitive x = 0 := by
  have he : (∫ s in (0 : ℝ)..x, Real.smoothTransition s) = ∫ _ in (0 : ℝ)..x, (0 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_ge hx] at hs
    exact Real.smoothTransition.zero_of_nonpos hs.2
  simpa only [smoothPositivePrimitive,intervalIntegral.integral_zero] using he

theorem smoothPositivePrimitive_affine_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    smoothPositivePrimitive x = x-1+smoothPositivePrimitive 1 := by
  have he : (∫ s in (1 : ℝ)..x, Real.smoothTransition s) = x-1 := by
    calc
      _ = ∫ _ in (1 : ℝ)..x, (1 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le hx] at hs
        exact Real.smoothTransition.one_of_one_le hs.1
      _ = _ := by simp
  have ha := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (Real.smoothTransition.continuous.intervalIntegrable (0 : ℝ) 1)
    (Real.smoothTransition.continuous.intervalIntegrable (1 : ℝ) x)
  rw [he] at ha
  dsimp only [smoothPositivePrimitive]
  linarith

theorem smoothPositivePrimitive_one_mem_Icc : smoothPositivePrimitive 1 ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact intervalIntegral.integral_nonneg_of_forall zero_le_one Real.smoothTransition.nonneg
  · have hh := intervalIntegral.integral_mono_on (μ := volume) zero_le_one
      (Real.smoothTransition.continuous.intervalIntegrable (0 : ℝ) 1)
      (continuous_const.intervalIntegrable (0 : ℝ) 1)
      (fun s _ => Real.smoothTransition.le_one s)
    simpa [smoothPositivePrimitive] using hh

theorem smoothPositivePrimitive_deriv_mem_Icc (x : ℝ) :
    deriv smoothPositivePrimitive x ∈ Icc (0 : ℝ) 1 := by
  rw [smoothPositivePrimitive_deriv]
  exact ⟨Real.smoothTransition.nonneg x,Real.smoothTransition.le_one x⟩

theorem smoothPositivePrimitive_second_deriv_nonneg (x : ℝ) :
    0 ≤ deriv (deriv smoothPositivePrimitive) x := by
  rw [smoothPositivePrimitive_deriv]
  exact Real.smoothTransition.monotone.deriv_nonneg

end PowerConvexity
