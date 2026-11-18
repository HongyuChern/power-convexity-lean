import PowerConvexity.Analysis.ActualGeometricBallAverageTwo

/-! # Identifying the actual quadratic field with the original weak function

The original L2 error controls the actual ball average. Lebesgue differentiation
then identifies the diagonal polynomial value almost everywhere; continuity of
the weak function is never assumed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_ball_average_L2_quadratic_bound_two
    {w : E → ℝ} {x : E} {r C : ℝ} (hr : 0 < r) (hC : 0 ≤ C)
    (hw : MemLp w 2 (volume.restrict (ball x r)))
    (herr : (∫ y in ball x r, (w y)^2) ≤ C*r^8) :
    |⨍ y in ball x r, w y| ≤
      ((C+1)*((volume (ball (0 : E) 1)).toReal+1)/(volume (ball (0 : E) 1)).toReal)*r^2 := by
  let V := (volume (ball (0 : E) 1)).toReal
  have hV : 0 < V := ENNReal.toReal_pos (measure_ball_pos volume (0 : E) zero_lt_one).ne'
    measure_ball_lt_top.ne
  have hvol : (volume (ball x r)).toReal = r^4*V := actual_four_ball_volume_scaling_two hr
  have hn : ‖hw.toLp w‖ ≤ (C+1)*r^4 := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ (C+1)*r^4)).mp
    rw [actual_scalar_L2_norm_squared_two hw,show ((C+1)*r^4)^2 = (C+1)^2*r^8 by ring]
    exact herr.trans (mul_le_mul_of_nonneg_right (by nlinarith : C ≤ (C+1)^2) (by positivity))
  have hone := actual_continuous_ball_memLp_two (continuous_const : Continuous (fun _ : E => (1 : ℝ))) x r
  have honeSq : ‖hone.toLp (fun _ => (1 : ℝ))‖^2 = r^4*V := by
    rw [actual_scalar_L2_norm_squared_two hone]
    simpa only [one_pow,integral_const,smul_eq_mul,mul_one,Measure.real,Measure.restrict_apply_univ] using hvol
  have honeN : ‖hone.toLp (fun _ => (1 : ℝ))‖ ≤ (V+1)*r^2 := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ (V+1)*r^2)).mp
    rw [honeSq,show ((V+1)*r^2)^2 = (V+1)^2*r^4 by ring]
    have hh : V ≤ (V+1)^2 := by nlinarith
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right hh (pow_nonneg hr.le 4)
  have hI : |∫ y in ball x r, w y| ≤ ((C+1)*r^4)*((V+1)*r^2) := by
    have hh := scalar_L2_integral_mul_bound hw hone
    simp only [mul_one] at hh
    exact hh.trans (mul_le_mul hn honeN (norm_nonneg _) (by positivity))
  rw [setAverage_eq,smul_eq_mul,abs_mul]
  change |(volume (ball x r)).toReal⁻¹| * |∫ y in ball x r, w y| ≤ _
  rw [hvol,abs_of_nonneg (by positivity : 0 ≤ (r^4*V)⁻¹)]
  exact (mul_le_mul_of_nonneg_left hI (by positivity)).trans_eq (by
    change (r^4*V)⁻¹*(((C+1)*r^4)*((V+1)*r^2)) = ((C+1)*(V+1)/V)*r^2
    field_simp
    <;> ring)

theorem actual_quadratic_L2_ball_average_tendsto_two
    {u p : E → ℝ} (hp : IsQuadraticPolynomial p) {x : E} {R theta C : ℝ}
    (hR : 0 < R) (htheta : 0 < theta) (htheta1 : theta < 1) (hC : 0 ≤ C)
    (hu : MemLp u 2 (volume.restrict (ball x R)))
    (herr : ∀ n : ℕ, (∫ y in ball x (R*theta^n), (u y-p y)^2) ≤
      C*((1/2 : ℝ)^n)^2*(R*theta^n)^8) :
    Tendsto (fun n : ℕ => ⨍ y in ball x (R*theta^n), u y) atTop (𝓝 (p x)) := by
  let V := (volume (ball (0 : E) 1)).toReal
  let K := (C+1)*(V+1)/V
  have hrad := (actual_geometric_radius_tendsto_two hR htheta htheta1).mono_right nhdsWithin_le_nhds
  have he (n : ℕ) : (⨍ y in ball x (R*theta^n), u y-p y) =
      (⨍ y in ball x (R*theta^n), u y)-(⨍ y in ball x (R*theta^n), p y) := by
    letI : IsFiniteMeasure (volume.restrict (ball x (R*theta^n))) :=
      isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
    have hum : MemLp u 2 (volume.restrict (ball x (R*theta^n))) := hu.mono_measure (Measure.restrict_mono
      (ball_subset_ball (mul_le_of_le_one_right hR.le (pow_le_one₀ htheta.le htheta1.le))) le_rfl)
    have hpm := actual_continuous_ball_memLp_two (IsQuadraticPolynomial_contDiff hp 0).continuous x (R*theta^n)
    exact integral_sub (hum.integrable (by norm_num : (1 : ENNReal) ≤ 2)).to_average
      (hpm.integrable (by norm_num : (1 : ENNReal) ≤ 2)).to_average
  have hlim : Tendsto (fun n : ℕ => ⨍ y in ball x (R*theta^n), u y-p y) atTop (𝓝 0) := by
    have hKlim : Tendsto (fun n : ℕ => K*(R*theta^n)^2) atTop (𝓝 0) := by
      simpa only [zero_pow (by decide : 2 ≠ 0),mul_zero] using (hrad.pow 2).const_mul K
    apply Metric.tendsto_nhds.mpr
    intro epsilon hepsilon
    filter_upwards [hKlim.eventually (gt_mem_nhds hepsilon)] with n hn
    have hrn := mul_pos hR (pow_pos htheta n)
    have hum : MemLp u 2 (volume.restrict (ball x (R*theta^n))) := hu.mono_measure (Measure.restrict_mono
      (ball_subset_ball (mul_le_of_le_one_right hR.le (pow_le_one₀ htheta.le htheta1.le))) le_rfl)
    have hpm := actual_continuous_ball_memLp_two (IsQuadraticPolynomial_contDiff hp 0).continuous x (R*theta^n)
    have hw : MemLp (fun y => u y-p y) 2 (volume.restrict (ball x (R*theta^n))) := hum.sub hpm
    have hE : (∫ y in ball x (R*theta^n), (u y-p y)^2) ≤ C*(R*theta^n)^8 := by
      apply (herr n).trans
      have hb : ((1/2 : ℝ)^n)^2 ≤ 1 := pow_le_one₀ (by positivity)
        (pow_le_one₀ (by norm_num) (by norm_num))
      have hh := mul_le_of_le_one_right hC hb
      exact mul_le_mul_of_nonneg_right hh (by positivity)
    have hb := actual_ball_average_L2_quadratic_bound_two hrn hC hw hE
    simpa only [Real.dist_eq,sub_zero] using hb.trans_lt hn
  have hpLim := actual_continuous_geometric_ball_average_tendsto_two
    (IsQuadraticPolynomial_contDiff hp 0).continuous x hR htheta htheta1
  have hsum := hlim.add hpLim
  simpa only [he,sub_add_cancel,zero_add] using hsum

theorem actual_polynomial_field_ae_eq_of_uniform_L2_two
    {U V : Set E} (hV : IsOpen V) (hVb : Bornology.IsBounded V) (hVU : V ⊆ U)
    {u : E → ℝ} (hu : MemLp u 2 (volume.restrict U))
    (P : E → E → ℝ) (hP : ∀ x ∈ V, IsQuadraticPolynomial (P x))
    {R theta C : ℝ} (hR : 0 < R) (htheta : 0 < theta) (htheta1 : theta < 1) (hC : 0 ≤ C)
    (hballs : ∀ x ∈ V, ball x R ⊆ U)
    (herr : ∀ x ∈ V, ∀ n : ℕ,
      (∫ z in ball x (R*theta^n), (u z-P x z)^2) ≤
        C*((1/2 : ℝ)^n)^2*(R*theta^n)^8) :
    (fun x => P x x) =ᵐ[volume.restrict V] u := by
  letI : IsFiniteMeasure (volume.restrict V) := isFiniteMeasure_restrict.mpr hVb.measure_lt_top.ne
  have huv := hu.mono_measure (Measure.restrict_mono hVU le_rfl)
  have hdiff := actual_ae_geometric_ball_average_tendsto_two hV
    (huv.integrable (by norm_num : (1 : ENNReal) ≤ 2)) hR htheta htheta1
  filter_upwards [hdiff,ae_restrict_mem hV.measurableSet] with x hx hxV
  exact tendsto_nhds_unique (actual_quadratic_L2_ball_average_tendsto_two (hP x hxV)
    hR htheta htheta1 hC (hu.mono_measure (Measure.restrict_mono (hballs x hxV) le_rfl))
    (herr x hxV)) hx

end PowerConvexity
