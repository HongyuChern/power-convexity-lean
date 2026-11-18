import PowerConvexity.Analysis.ActualGeometricScaleSelectionTwo
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Exact power moduli at the actual geometric approximation scales -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Set Filter Metric
open scoped Topology
namespace PowerConvexity

theorem actual_positive_power_radius_two {alpha : ℝ} (halpha : 0 < alpha) :
    ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, 0 ≤ r → r ≤ R → r^alpha ≤ (1/2 : ℝ) := by
  refine ⟨(1/2 : ℝ)^alpha⁻¹,Real.rpow_pos_of_pos (by norm_num) _,?_⟩
  intro r hr hrR
  exact (Real.rpow_le_rpow hr hrR halpha.le).trans_eq
    (Real.rpow_inv_rpow (by norm_num : (0 : ℝ) ≤ 1/2) halpha.ne')

theorem actual_nat_power_rpow_comm_two {r : ℝ} (hr : 0 ≤ r) (alpha : ℝ) (n : ℕ) :
    (r^n)^alpha = (r^alpha)^n := by
  rw [← Real.rpow_natCast_mul hr,← Real.rpow_mul_natCast hr]
  congr 1
  ring

theorem actual_geometric_rpow_half_bound_two {r alpha d : ℝ}
    (hr : 0 ≤ r) (halpha : 0 ≤ alpha) (hpow : r^alpha ≤ (1/2 : ℝ))
    (n : ℕ) (hd : 0 ≤ d) (hdr : d ≤ r^n) : d^alpha ≤ (1/2 : ℝ)^n := by
  calc
    d^alpha ≤ (r^n)^alpha := Real.rpow_le_rpow hd hdr halpha
    _ = (r^alpha)^n := actual_nat_power_rpow_comm_two hr alpha n
    _ ≤ (1/2 : ℝ)^n := pow_le_pow_left₀ (Real.rpow_nonneg hr _) hpow n

theorem actual_half_decay_exponent_two {theta : ℝ} (htheta : 0 < theta) (htheta1 : theta < 1) :
    ∃ beta : ℝ, 0 < beta ∧ beta < 1 ∧ (1/2 : ℝ) ≤ theta^beta := by
  let beta : ℝ := theta/2
  have hb : 0 < beta := half_pos htheta
  have hb1 : beta < 1 := by dsimp only [beta]; linarith
  have hl := Real.log_le_sub_one_of_pos (inv_pos.mpr htheta)
  rw [Real.log_inv] at hl
  have hlt := mul_le_mul_of_nonneg_right hl htheta.le
  rw [sub_mul,inv_mul_cancel₀ htheta.ne',one_mul] at hlt
  refine ⟨beta,hb,hb1,?_⟩
  rw [Real.rpow_def_of_pos htheta]
  have he := Real.add_one_le_exp (Real.log theta*beta)
  dsimp only [beta] at he ⊢
  nlinarith

theorem actual_geometric_half_radius_holder_select_two
    {R theta beta d : ℝ} (hR : 0 < R) (htheta : 0 < theta) (htheta1 : theta < 1)
    (hbeta : 0 ≤ beta) (hdecay : (1/2 : ℝ) ≤ theta^beta)
    (hd : 0 < d) (hsmall : d < R/2) :
    ∃ k : ℕ, d ≤ R*theta^k/2 ∧
      (1/2 : ℝ)^k ≤ (2/(R*theta))^beta*d^beta := by
  obtain ⟨k,hlo,hhi⟩ := actual_geometric_half_radius_select_two hR htheta htheta1 0 hd
    (by simpa only [pow_zero,mul_one] using hsmall)
  simp only [zero_add] at hlo hhi
  have hkn : theta^k ≤ (2/(R*theta))*d := by
    have hhi' := (lt_div_iff₀ htheta).mp hhi
    have hh : theta^k ≤ (2*d)/(R*theta) := by
      apply (le_div_iff₀ (mul_pos hR htheta)).mpr
      nlinarith
    exact hh.trans_eq (by ring)
  refine ⟨k,hlo,?_⟩
  calc
    (1/2 : ℝ)^k ≤ (theta^beta)^k := pow_le_pow_left₀ (by norm_num) hdecay k
    _ = (theta^k)^beta := (actual_nat_power_rpow_comm_two htheta.le beta k).symm
    _ ≤ ((2/(R*theta))*d)^beta := Real.rpow_le_rpow (pow_nonneg htheta.le k) hkn hbeta
    _ = (2/(R*theta))^beta*d^beta := Real.mul_rpow (by positivity) hd.le

end PowerConvexity
