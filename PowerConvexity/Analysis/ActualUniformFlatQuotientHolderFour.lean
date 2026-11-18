import PowerConvexity.Analysis.ActualUniformFlatQuotientLimitFour
import PowerConvexity.Analysis.ActualGeometricHolderScaleTwo

/-! # A common power modulus for the actual boundary quotient

The exponent and constant are chosen before the normal and all equation
data. The final remainder is bounded by distance to the flat boundary times
a positive power of the distance to its basepoint.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_quotient_decay_exponent_four {r q : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hq : 0 < q) (hq1 : q < 1) :
    ∃ alpha : ℝ, 0 < alpha ∧ alpha < 1 ∧ q ≤ r^alpha := by
  let alpha := r*(1-q)
  have ha : 0 < alpha := mul_pos hr (by linarith)
  have ha1 : alpha < 1 := by
    have hp := mul_pos hr hq
    dsimp only [alpha]
    nlinarith
  have hl := Real.log_le_sub_one_of_pos (inv_pos.mpr hr)
  rw [Real.log_inv] at hl
  have hlt := mul_le_mul_of_nonneg_right hl hr.le
  rw [sub_mul,inv_mul_cancel₀ hr.ne',one_mul] at hlt
  have hlt' := mul_le_mul_of_nonneg_right hlt (show 0 ≤ 1-q by linarith)
  refine ⟨alpha,ha,ha1,?_⟩
  rw [Real.rpow_def_of_pos hr]
  have he := Real.add_one_le_exp (Real.log r*alpha)
  dsimp only [alpha] at he ⊢
  nlinarith [mul_nonneg hr.le (show 0 ≤ 1-q by linarith)]

theorem actual_flat_geometric_quotient_holder_four {r q alpha M : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hq : 0 ≤ q) (ha : 0 < alpha)
    (hdecay : q ≤ r^alpha) (hM : 0 ≤ M) (N : E) (u : E → ℝ) (a : ℝ)
    (herr : ∀ n : ℕ, ∀ x ∈ actualFlatClosedUpperBallFour N (r^n),
      |u x-a*inner ℝ N x| ≤ M*q^n*inner ℝ N x) :
    ∀ x ∈ actualFlatClosedUpperBallFour N 1,
      |u x-a*inner ℝ N x| ≤ (M*(r⁻¹)^alpha)*‖x‖^alpha*inner ℝ N x := by
  intro x hx
  have hxN : 0 ≤ inner ℝ N x := hx.2
  by_cases hx0 : x=0
  · subst x
    have hh := herr 0 0 (by simpa only [pow_zero] using hx)
    simpa only [inner_zero_right,mul_zero] using hh
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hx1 : ‖x‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using hx.1
  obtain ⟨n,hlo,hhi⟩ := exists_nat_pow_near_of_lt_one hxpos hx1 hr hr1
  have hn : r^n ≤ r⁻¹*‖x‖ := by
    calc
      r^n ≤ ‖x‖/r := (le_div_iff₀ hr).mpr (by simpa only [pow_succ] using hlo.le)
      _ = r⁻¹*‖x‖ := by ring
  have hqpow : q^n ≤ (r⁻¹)^alpha*‖x‖^alpha := by
    calc
      q^n ≤ (r^alpha)^n := pow_le_pow_left₀ hq hdecay n
      _ = (r^n)^alpha := (actual_nat_power_rpow_comm_two hr.le alpha n).symm
      _ ≤ (r⁻¹*‖x‖)^alpha := Real.rpow_le_rpow (pow_nonneg hr.le n) hn ha.le
      _ = (r⁻¹)^alpha*‖x‖^alpha := Real.mul_rpow (inv_nonneg.mpr hr.le) hxpos.le
  have hxr : x ∈ actualFlatClosedUpperBallFour N (r^n) :=
    ⟨by simpa only [mem_closedBall,dist_zero_right] using hhi,hxN⟩
  calc
    |u x-a*inner ℝ N x| ≤ M*q^n*inner ℝ N x := herr n x hxr
    _ ≤ M*((r⁻¹)^alpha*‖x‖^alpha)*inner ℝ N x :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hqpow hM) hxN
    _ = _ := by ring

theorem actual_uniform_flat_boundary_quotient_holder_four {Lambda : ℝ} (hLambda : 1 ≤ Lambda) :
    ∃ alpha : ℝ, 0 < alpha ∧ alpha < 1 ∧ ∃ C > 0,
      ∀ N : E, ‖N‖=1 → ∀ B ≥ 0, B ≤ 1/2 → ∀ F > 0,
      ∀ D : ActualFlatQuotientEquationFour N Lambda B F,
      ∀ S ≥ 0, ∀ I0 : ActualFlatSlopeIntervalFour N D.solution 1 S,
      ∃ a : ℝ, |a| ≤ S ∧ ∀ x ∈ actualFlatClosedUpperBallFour N 1,
        |D.solution x-a*inner ℝ N x| ≤ C*(S+F+B*S)*‖x‖^alpha*inner ℝ N x := by
  obtain ⟨q,hq,hq1,C0,hC0,hlimit⟩ := actual_uniform_flat_boundary_quotient_limit_four hLambda
  obtain ⟨alpha,ha,ha1,hdecay⟩ := actual_quotient_decay_exponent_four
    (r := 1/64) (by norm_num) (by norm_num) hq hq1
  let C := (2+C0)*(((1/64 : ℝ)⁻¹)^alpha)
  have hC : 0 < C := mul_pos (by linarith) (Real.rpow_pos_of_pos (by norm_num) _)
  refine ⟨alpha,ha,ha1,C,hC,?_⟩
  intro N hN B hB hBsmall F hF D S hS I0
  obtain ⟨a,haS,herr⟩ := hlimit N hN B hB hBsmall F hF D S hS I0
  have hM : 0 ≤ 2*S+C0*(F+B*S) := by positivity
  have hp := actual_flat_geometric_quotient_holder_four (by norm_num : (0 : ℝ) < 1/64)
    (by norm_num : (1/64 : ℝ) < 1) hq.le ha hdecay hM N D.solution a herr
  have hcoef : 2*S+C0*(F+B*S) ≤ (2+C0)*(S+F+B*S) := by
    nlinarith [mul_nonneg hC0.le hS,mul_nonneg hB hS]
  refine ⟨a,haS,?_⟩
  intro x hx
  have ht : 0 ≤ inner ℝ N x := hx.2
  calc
    |D.solution x-a*inner ℝ N x| ≤
      ((2*S+C0*(F+B*S))*((1/64 : ℝ)⁻¹)^alpha)*‖x‖^alpha*inner ℝ N x := hp x hx
    _ ≤ (((2+C0)*(S+F+B*S))*((1/64 : ℝ)⁻¹)^alpha)*‖x‖^alpha*inner ℝ N x := by
      gcongr
    _ = C*(S+F+B*S)*‖x‖^alpha*inner ℝ N x := by dsimp only [C]; ring

end PowerConvexity
