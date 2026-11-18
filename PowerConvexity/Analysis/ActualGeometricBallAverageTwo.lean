import PowerConvexity.Analysis.ActualUniformQuadraticJetCompatibilityTwo
import DifferentialGeometry.External.DeGiorgi.Oscillation.Campanato

/-! # Actual geometric ball averages and almost-everywhere differentiation -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_geometric_radius_tendsto_two {R theta : ℝ}
    (hR : 0 < R) (htheta : 0 < theta) (htheta1 : theta < 1) :
    Tendsto (fun n : ℕ => R*theta^n) atTop (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_,Eventually.of_forall (fun n => mul_pos hR (pow_pos htheta n))⟩
  simpa only [mul_zero] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one htheta.le htheta1).const_mul R

theorem actual_ae_geometric_ball_average_tendsto_two
    {U : Set E} (hU : IsOpen U) {u : E → ℝ} (hu : IntegrableOn u U)
    {R theta : ℝ} (hR : 0 < R) (htheta : 0 < theta) (htheta1 : theta < 1) :
    ∀ᵐ x ∂volume.restrict U,
      Tendsto (fun n : ℕ => ⨍ y in ball x (R*theta^n), u y) atTop (𝓝 (u x)) := by
  let f : E → ℝ := U.indicator u
  have hf : Integrable f volume := hu.integrable_indicator hU.measurableSet
  have hrad := actual_geometric_radius_tendsto_two hR htheta htheta1
  have hdiff : ∀ᵐ x ∂volume,
      Tendsto (fun n : ℕ => ⨍ y in closedBall x (R*theta^n), f y) atTop (𝓝 (f x)) := by
    filter_upwards [((IsUnifLocDoublingMeasure.vitaliFamily (μ := volume) (K := 0)).ae_tendsto_average
      hf.locallyIntegrable)] with x hx
    exact hx.comp (IsUnifLocDoublingMeasure.tendsto_closedBall_filterAt (μ := volume) (K := 0)
      (fun _ : ℕ => x) (fun n => R*theta^n) hrad
      (Eventually.of_forall (fun n => mem_closedBall_self (by positivity : (0 : ℝ) ≤ 0*(R*theta^n)))))
  rw [ae_restrict_iff' hU.measurableSet]
  filter_upwards [hdiff] with x hx hxU
  obtain ⟨delta,hd,hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hxU)
  have he : (fun n : ℕ => ⨍ y in closedBall x (R*theta^n), f y) =ᶠ[atTop]
      (fun n : ℕ => ⨍ y in ball x (R*theta^n), u y) := by
    filter_upwards [(hrad.mono_right nhdsWithin_le_nhds).eventually (gt_mem_nhds hd)] with n hn
    rw [setAverage_closedBall_eq_ball_of_pos x (mul_pos hR (pow_pos htheta n))]
    apply setAverage_congr_fun measurableSet_ball
    exact Eventually.of_forall (fun y hy => by
      have hyU := hball ((ball_subset_ball hn.le) hy)
      exact Set.indicator_of_mem hyU u)
  have hx' : Tendsto (fun n : ℕ => ⨍ y in closedBall x (R*theta^n), f y) atTop (𝓝 (u x)) := by
    simpa only [f,Set.indicator_of_mem hxU] using hx
  exact hx'.congr' he

theorem actual_ball_average_norm_bound_two {q : E → ℝ} {x : E} {r M : ℝ}
    (hr : 0 < r) (hq : ∀ y ∈ ball x r, ‖q y‖ ≤ M) :
    ‖⨍ y in ball x r, q y‖ ≤ M := by
  have hvol : 0 < (volume (ball x r)).toReal :=
    ENNReal.toReal_pos (measure_ball_pos volume x hr).ne' measure_ball_lt_top.ne
  rw [setAverage_eq,smul_eq_mul,norm_mul,Real.norm_eq_abs,Measure.real,
    abs_of_nonneg (inv_nonneg.mpr hvol.le)]
  have hb := norm_setIntegral_le_of_norm_le_const (μ := volume) measure_ball_lt_top hq
  exact (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hvol.le)).trans_eq (by
    change (volume (ball x r)).toReal⁻¹*(M*(volume (ball x r)).toReal) = M
    field_simp)

theorem actual_continuous_geometric_ball_average_tendsto_two
    {q : E → ℝ} (hq : Continuous q) (x : E) {R theta : ℝ}
    (hR : 0 < R) (htheta : 0 < theta) (htheta1 : theta < 1) :
    Tendsto (fun n : ℕ => ⨍ y in ball x (R*theta^n), q y) atTop (𝓝 (q x)) := by
  have hrad := (actual_geometric_radius_tendsto_two hR htheta htheta1).mono_right nhdsWithin_le_nhds
  apply Metric.tendsto_nhds.mpr
  intro epsilon hepsilon
  obtain ⟨delta,hd,hnear⟩ := Metric.continuousAt_iff.mp hq.continuousAt (epsilon/2) (by positivity)
  filter_upwards [hrad.eventually (gt_mem_nhds hd)] with n hn
  have hrn := mul_pos hR (pow_pos htheta n)
  letI : IsFiniteMeasure (volume.restrict (ball x (R*theta^n))) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hqm := actual_continuous_ball_memLp_two hq x (R*theta^n)
  have hqi := hqm.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have he : (⨍ y in ball x (R*theta^n), q y-q x) =
      (⨍ y in ball x (R*theta^n), q y)-q x := by
    have hh := integral_sub hqi.to_average (integrable_const (q x)).to_average
    change (⨍ y in ball x (R*theta^n), q y-q x) =
      (⨍ y in ball x (R*theta^n), q y)-(⨍ _ in ball x (R*theta^n), q x) at hh
    simpa only [setAverage_const (measure_ball_pos volume x hrn).ne' measure_ball_lt_top.ne] using hh
  rw [dist_eq_norm,← he]
  apply (actual_ball_average_norm_bound_two hrn ?_).trans_lt (by linarith : epsilon/2 < epsilon)
  intro y hy
  have hynear : dist y x < delta := lt_trans hy hn
  simpa only [dist_eq_norm] using (hnear hynear).le

end PowerConvexity
