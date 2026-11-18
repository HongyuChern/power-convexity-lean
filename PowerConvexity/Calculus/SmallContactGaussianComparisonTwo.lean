import PowerConvexity.Calculus.SmallContactGaussianBarrierTwo

/-! # Actual annular comparison for the shifted determinant-one equation.
The one fixed opening threshold is independent of the radius and centre.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
local notation "E" => DeGiorgi.AmbientSpace (2+2)

theorem normalized_gaussian_weight_bounds_two
    {k r : ℝ} (hk : 0 ≤ k) (hr : 0 < r) {c x : E} (hx : ‖x-c‖ ≤ r) :
    1 ≤ Real.exp k*radialGaussian (k/r^2) c x ∧
      Real.exp k*radialGaussian (k/r^2) c x ≤ Real.exp k := by
  have hkdiv : 0 ≤ k/r^2 := div_nonneg hk (sq_nonneg r)
  have hsq : ‖x-c‖^2 ≤ r^2 := (sq_le_sq₀ (norm_nonneg _) hr.le).mpr hx
  have hb : k/r^2*‖x-c‖^2 ≤ k := by
    calc
      _ ≤ k/r^2*r^2 := mul_le_mul_of_nonneg_left hsq hkdiv
      _ = k := div_mul_cancel₀ _ (pow_ne_zero 2 hr.ne')
  have hn := mul_nonneg hkdiv (sq_nonneg ‖x-c‖)
  rw [radialGaussian,← Real.exp_add]
  constructor
  · simpa only [Real.exp_zero] using
      (Real.exp_le_exp.mpr (show 0 ≤ k+(-(k/r^2))*‖x-c‖^2 by linarith only [hb]))
  · exact Real.exp_le_exp.mpr (by linarith only [hn])

theorem bumpedLowerParaboloidTwo_quadratic_lower
    {a k r : ℝ} (ha : 0 ≤ a) (hk : 0 < k) (hr : 0 < r) (c y x v : E) :
    -(a*(1+Real.exp k*radialGaussian (k/r^2) c x)*‖v‖^2) ≤
      realHessian (bumpedLowerParaboloidTwo a k r c y) x v v := by
  rw [bumpedLowerParaboloidTwo_realHessian hk.ne' hr.ne',real_inner_self_eq_norm_sq]
  have hp : 0 ≤ a*(Real.exp k*radialGaussian (k/r^2) c x)*
      (2*k/r^2)*(inner ℝ (x-c) v)^2 := by
    unfold radialGaussian
    positivity
  nlinarith only [hp]

theorem contact_gaussian_annular_coefficient_lower_two
    {r : ℝ} (hr : 0 < r) {c x : E} (hx : r/16 ≤ ‖x-c‖) :
    32 ≤ (2*(4096 : ℝ)/r^2)*‖x-c‖^2 := by
  have hs : (r/16)^2 ≤ ‖x-c‖^2 :=
    (sq_le_sq₀ (by positivity : 0 ≤ r/16) (norm_nonneg _)).mpr hx
  calc
    32 = (2*(4096 : ℝ)/r^2)*(r/16)^2 := by field_simp; ring
    _ ≤ (2*(4096 : ℝ)/r^2)*‖x-c‖^2 := mul_le_mul_of_nonneg_left hs (by positivity)

theorem bumpedLowerParaboloidTwo_annular_strict_trace
    {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (c y x : E)
    (hxlo : r/16 ≤ ‖x-c‖) (hxhi : ‖x-c‖ ≤ r) :
    4*(a*(1+Real.exp 4096*radialGaussian (4096/r^2) c x)) <
      (realBlockHessian realDirections imagDirections
        (bumpedLowerParaboloidTwo a 4096 r c y) x).trace := by
  have hF := (normalized_gaussian_weight_bounds_two (by norm_num : (0 : ℝ) ≤ 4096) hr hxhi).1
  have hL := contact_gaussian_annular_coefficient_lower_two hr hxlo
  have hp := mul_le_mul_of_nonneg_left hL (le_trans (by norm_num : (0 : ℝ) ≤ 1) hF)
  rw [bumpedLowerParaboloidTwo_trace (by norm_num : (4096 : ℝ) ≠ 0) hr.ne']
  have hh : 4*(1+Real.exp 4096*radialGaussian (4096/r^2) c x) <
      (Real.exp 4096*radialGaussian (4096/r^2) c x)*
        ((2*4096/r^2)*‖x-c‖^2-4)-4 := by
    nlinarith only [hF,hp]
  have h := mul_lt_mul_of_pos_left hh ha
  simpa only [mul_assoc,mul_left_comm,mul_comm] using h

theorem small_contact_gaussian_no_annular_lower_contact_two
    {w : E → ℝ} {x c y : E} (hw : ContDiffAt ℝ 2 w x)
    {a r : ℝ} (ha : 0 < a) (hr : 0 < r)
    (hsmall : a ≤ (1+Real.exp 4096)⁻¹)
    (hdet : (1+complexHessian realDirections imagDirections w x).det = 1)
    (hxlo : r/16 ≤ ‖x-c‖) (hxhi : ‖x-c‖ ≤ r) :
    ¬ IsLocalMin (fun z => w z-bumpedLowerParaboloidTwo a 4096 r c y z) x := by
  let b : ℝ := a*(1+Real.exp 4096*radialGaussian (4096/r^2) c x)
  have hb : 0 ≤ b := by unfold b radialGaussian; positivity
  have hF := (normalized_gaussian_weight_bounds_two (by norm_num : (0 : ℝ) ≤ 4096) hr hxhi).2
  have hden : 0 < 1+Real.exp (4096 : ℝ) := by positivity
  have haD : a*(1+Real.exp 4096) ≤ 1 :=
    (le_div_iff₀ hden).mp (by simpa only [one_div] using hsmall)
  have hb1 : b ≤ 1 :=
    (mul_le_mul_of_nonneg_left (add_le_add le_rfl hF) ha.le).trans haD
  apply actual_small_strict_trace_barrier_no_lower_contact_two hw
    (bumpedLowerParaboloidTwo_contDiff a 4096 r c y 2).contDiffAt hb hb1 hdet
  · exact bumpedLowerParaboloidTwo_quadratic_lower ha.le (by norm_num) hr c y x
  · exact bumpedLowerParaboloidTwo_annular_strict_trace ha hr c y x hxlo hxhi

end PowerConvexity
