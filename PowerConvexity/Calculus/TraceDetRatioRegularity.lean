import PowerConvexity.Algebra.TraceDetRatioTwo
import PowerConvexity.Calculus.RealHessianRules
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Regularity and dominating smooth approximations of trace+det/trace

At zero trace, differentiability follows from the actual trace derivative and
0 ≤ det ≤ trace²/4; a C2 extension at the repeated zero is not assumed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Filter Set
open scoped Topology ContDiff
namespace PowerConvexity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem traceDetRatioTwo_hasFDerivAt_zero {t d : E → ℝ} {x : E}
    (ht : DifferentiableAt ℝ t x) (ht0 : t x = 0)
    (hnear : ∀ᶠ y in 𝓝 x, 0 ≤ t y ∧ 0 ≤ d y ∧ d y ≤ (t y)^2/4) :
    HasFDerivAt (fun y => traceDetRatioTwo (t y) (d y)) (0 : E →L[ℝ] ℝ) x := by
  have hm : IsLocalMin t x := by
    filter_upwards [hnear] with y hy
    simpa only [ht0] using hy.1
  have hDt : HasFDerivAt t (0 : E →L[ℝ] ℝ) x := by simpa only [hm.fderiv_eq_zero] using ht.hasFDerivAt
  have hf0 : traceDetRatioTwo (t x) (d x) = 0 := by simp [traceDetRatioTwo,ht0]
  apply HasFDerivAt.of_isLittleO
  apply Asymptotics.IsLittleO.of_bound
  intro c hc
  have hs := hDt.isLittleO.bound (half_pos hc)
  filter_upwards [hnear,hs] with y hy hsmall
  have hb := traceDetRatioTwo_bounds hy.1 hy.2.1 hy.2.2
  have hfnon : 0 ≤ traceDetRatioTwo (t y) (d y) := hy.1.trans hb.1
  simp only [ContinuousLinearMap.zero_apply,sub_zero,ht0,Real.norm_eq_abs,
    abs_of_nonneg hy.1] at hsmall
  simp only [hf0,ContinuousLinearMap.zero_apply,sub_zero,Real.norm_eq_abs,
    abs_of_nonneg hfnon]
  nlinarith [norm_nonneg (y-x)]

theorem traceDetRatioTwo_differentiableAt {t d : E → ℝ} {x : E}
    (ht : DifferentiableAt ℝ t x) (hd : DifferentiableAt ℝ d x)
    (hnear : ∀ᶠ y in 𝓝 x, 0 ≤ t y ∧ 0 ≤ d y ∧ d y ≤ (t y)^2/4) :
    DifferentiableAt ℝ (fun y => traceDetRatioTwo (t y) (d y)) x := by
  by_cases hx : t x = 0
  · exact (traceDetRatioTwo_hasFDerivAt_zero ht hx hnear).differentiableAt
  · simpa only [traceDetRatioTwo,div_eq_mul_inv] using ht.fun_add (hd.fun_mul (ht.fun_inv hx))

theorem traceDetRatioTwo_contDiffAt_of_pos {t d : E → ℝ} {x : E}
    (ht : ContDiffAt ℝ 2 t x) (hd : ContDiffAt ℝ 2 d x) (hx : t x ≠ 0) :
    ContDiffAt ℝ 2 (fun y => traceDetRatioTwo (t y) (d y)) x :=
  ht.add (hd.div ht hx)

theorem traceDetRatioTwo_regularized_contDiffAt {t d : E → ℝ} {x : E}
    (ht : ContDiffAt ℝ 2 t x) (hd : ContDiffAt ℝ 2 d x)
    (hx : 0 ≤ t x) {e : ℝ} (he : 0 < e) :
    ContDiffAt ℝ 2 (fun y => traceDetRatioTwo (t y+2*e) (d y+e*t y+e^2)) x := by
  exact traceDetRatioTwo_contDiffAt_of_pos (ht.add contDiffAt_const)
    ((hd.add (contDiffAt_const.mul ht)).add contDiffAt_const) (by positivity)

theorem traceDetRatioTwo_regularization_tendsto {T : Type*} {l : Filter T}
    {e : T → ℝ} (he : ∀ᶠ s in l, 0 ≤ e s) (he0 : Tendsto e l (𝓝 0))
    {t d : ℝ} (ht : 0 ≤ t) (hd : 0 ≤ d) (hdt : d ≤ t^2/4) :
    Tendsto (fun s => traceDetRatioTwo (t+2*e s) (d+e s*t+(e s)^2)) l
      (𝓝 (traceDetRatioTwo t d)) := by
  have hupper : Tendsto (fun s => traceDetRatioTwo t d+3*e s) l
      (𝓝 (traceDetRatioTwo t d)) := by
    convert tendsto_const_nhds.add (tendsto_const_nhds.mul he0) using 1 <;> simp
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · exact he.mono fun s hs => (traceDetRatioTwo_regularization_bounds ht hd hdt hs).1
  · exact he.mono fun s hs => (traceDetRatioTwo_regularization_bounds ht hd hdt hs).2

end PowerConvexity
