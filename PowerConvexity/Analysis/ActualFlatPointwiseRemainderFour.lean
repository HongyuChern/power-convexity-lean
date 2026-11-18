import PowerConvexity.Analysis.ActualFlatPhysicalExpansionFour
import PowerConvexity.Analysis.ActualGeometricHolderScaleTwo

/-! # Actual pointwise boundary remainder from geometric half-ball expansions -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_flat_geometric_remainder_holder_four {R r C : ℝ}
    (hR : 0 < R) (hr : 0 < r) (hr1 : r < 1) (hC : 0 ≤ C) :
    ∃ beta : ℝ, 0 < beta ∧ beta < 1 ∧ ∃ M ≥ 0,
      ∀ (N : E) (u p : E → ℝ), u 0=p 0 →
      (∀ n : ℕ, ∀ x ∈ actualFlatClosedUpperBallFour N (R*r^n),
        |u x-p x| ≤ C*(1/2 : ℝ)^n*(R*r^n)^2) →
      ∀ x : E, 0 ≤ inner ℝ N x → ‖x‖ < R/2 →
        |u x-p x| ≤ M*‖x‖^2*‖x‖^beta := by
  obtain ⟨beta,hbeta,hbeta1,hdecay⟩ := actual_half_decay_exponent_two hr hr1
  let M := C*(2/(R*r))^beta*(2/r)^2
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  refine ⟨beta,hbeta,hbeta1,M,hM,?_⟩
  intro N u p hzero herr x hx hsmall
  by_cases hx0 : x=0
  · subst x
    rw [hzero,sub_self,abs_zero,norm_zero,zero_pow (by norm_num : 2 ≠ 0),mul_zero,zero_mul]
  have hd : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  obtain ⟨n,hlo,hhi⟩ := actual_geometric_half_radius_select_two hR hr hr1 0 hd
    (by simpa only [pow_zero,mul_one] using hsmall)
  simp only [zero_add] at hlo hhi
  have hn : r^n ≤ (2/(R*r))*‖x‖ := by
    have hh := (lt_div_iff₀ hr).mp hhi
    have hdiv : r^n ≤ (2*‖x‖)/(R*r) := by
      apply (le_div_iff₀ (mul_pos hR hr)).mpr
      nlinarith
    exact hdiv.trans_eq (by ring)
  have hp : (1/2 : ℝ)^n ≤ (2/(R*r))^beta*‖x‖^beta := by
    calc
      _ ≤ (r^beta)^n := pow_le_pow_left₀ (by norm_num) hdecay n
      _ = (r^n)^beta := (actual_nat_power_rpow_comm_two hr.le beta n).symm
      _ ≤ ((2/(R*r))*‖x‖)^beta := Real.rpow_le_rpow (pow_nonneg hr.le n) hn hbeta.le
      _ = _ := Real.mul_rpow (by positivity) hd.le
  have hs : R*r^n ≤ (2/r)*‖x‖ := by
    have hh := (lt_div_iff₀ hr).mp hhi
    have hdiv : R*r^n ≤ (2*‖x‖)/r := by
      apply (le_div_iff₀ hr).mpr
      nlinarith
    exact hdiv.trans_eq (by ring)
  have hsq : (R*r^n)^2 ≤ ((2/r)*‖x‖)^2 := by
    exact pow_le_pow_left₀ (mul_nonneg hR.le (pow_nonneg hr.le n)) hs 2
  have hm : x ∈ actualFlatClosedUpperBallFour N (R*r^n) := by
    refine ⟨?_,hx⟩
    rw [mem_closedBall,dist_zero_right]
    linarith [mul_pos hR (pow_pos hr n)]
  calc
    |u x-p x| ≤ C*(1/2 : ℝ)^n*(R*r^n)^2 := herr n x hm
    _ ≤ C*((2/(R*r))^beta*‖x‖^beta)*((2/r)*‖x‖)^2 := by gcongr
    _ = M*‖x‖^2*‖x‖^beta := by dsimp only [M]; ring

end PowerConvexity
