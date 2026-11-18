import PowerConvexity.Analysis.ActualQuadraticJetL2BoundTwo
import PowerConvexity.Analysis.ActualQuadraticScaleNormalizationTwo
import PowerConvexity.Analysis.ActualScalarQuadraticUpdateTwo
import PowerConvexity.Analysis.ActualQuadraticL2ErrorTwo
import PowerConvexity.Calculus.QuadraticHessianFromValues

/-! # Uniqueness of the quadratic determined by the actual L2 errors

The weak solution need not have a pointwise representative in this file.
Uniqueness concerns the actual polynomial, not a formal triple of jets.
The scale-sensitive polynomial estimate retains all three scaling powers.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_quadratic_scaled_L2_jet_bound_two :
    ∃ C > 0, ∀ (q : E → ℝ), IsQuadraticPolynomial q →
      ∀ R > 0, ∀ a ≥ 0,
      (∫ x in ball (0 : E) R, (q x)^2) ≤ a^2*R^8 →
        |q 0| ≤ C*a*R^2 ∧
        ‖fderiv ℝ q 0‖ ≤ C*a*R ∧ ‖realHessian q 0‖ ≤ C*a := by
  obtain ⟨C,hC,hjet⟩ := actual_quadratic_ball_L2_jet_bound_two (by norm_num : (0 : ℝ) < 1)
  refine ⟨C,hC,?_⟩
  intro q hq R hR a ha herr
  let p := scalarQuadraticLiftTwo R⁻¹ q
  have hp : IsQuadraticPolynomial p := scalarQuadraticLiftTwo_isQuadratic hq R⁻¹
  have hpm := actual_continuous_ball_memLp_two (IsQuadraticPolynomial_contDiff hp 0).continuous 0 1
  have he : p = fun z => (1 : ℝ)⁻¹*(R^2)⁻¹*q ((0 : E)+R • z) := by
    funext z
    simp only [p,scalarQuadraticLiftTwo_apply (inv_ne_zero hR.ne'),inv_inv,
      inv_pow,inv_one,one_mul,zero_add]
  have hn : ‖hpm.toLp p‖^2 = (R^8)⁻¹*(∫ x in ball (0 : E) R, (q x)^2) := by
    have hpm' : MemLp (fun z => (1 : ℝ)⁻¹*(R^2)⁻¹*q ((0 : E)+R • z)) 2
        (volume.restrict (ball (0 : E) 1)) := by simpa only [← he] using hpm
    have hi := actual_quadratic_scale_L2_identity_two hR (by norm_num : (0 : ℝ) < 1) q hpm'
    simpa only [← he,one_pow,one_mul] using hi
  have hnorm : ‖hpm.toLp p‖ ≤ a := by
    have hi := mul_le_mul_of_nonneg_left herr (inv_nonneg.mpr (pow_nonneg hR.le 8))
    have heq : (R^8)⁻¹*(a^2*R^8) = a^2 := by field_simp
    rw [heq,← hn] at hi
    nlinarith [norm_nonneg (hpm.toLp p)]
  obtain ⟨h0,h1,h2⟩ := hjet p hp hpm
  have hb0 : |p 0| ≤ C*a := h0.trans (mul_le_mul_of_nonneg_left hnorm hC.le)
  have hb1 : ‖fderiv ℝ p 0‖ ≤ C*a := h1.trans (mul_le_mul_of_nonneg_left hnorm hC.le)
  have hb2 : ‖realHessian p 0‖ ≤ C*a := h2.trans (mul_le_mul_of_nonneg_left hnorm hC.le)
  have hp0 : |p 0| = (R^2)⁻¹*|q 0| := by
    rw [he]
    simp only [inv_one,one_mul,smul_zero,zero_add,abs_mul,
      abs_of_pos (inv_pos.mpr (sq_pos_of_pos hR))]
  have hp1 : ‖fderiv ℝ p 0‖ = R⁻¹*‖fderiv ℝ q 0‖ := by
    rw [scalarQuadraticLiftTwo_fderiv_zero (inv_pos.mpr hR),norm_smul,
      Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hR)]
  have hp2 : realHessian p 0 = realHessian q 0 := by
    rw [scalarQuadraticLiftTwo_realHessian hq (inv_pos.mpr hR),smul_zero]
  rw [hp0] at hb0
  rw [hp1] at hb1
  rw [hp2] at hb2
  refine ⟨?_,?_,hb2⟩
  · have hh := mul_le_mul_of_nonneg_left hb0 (sq_nonneg R)
    simpa only [← mul_assoc,mul_inv_cancel₀ (pow_ne_zero 2 hR.ne'),one_mul,
      mul_comm (R^2) (C*a)] using hh
  · have hh := mul_le_mul_of_nonneg_left hb1 hR.le
    simpa only [← mul_assoc,mul_inv_cancel₀ hR.ne',one_mul,mul_comm R (C*a)] using hh

theorem actual_quadratic_zero_of_vanishing_scaled_L2_two
    {q : E → ℝ} (hq : IsQuadraticPolynomial q)
    (R a : ℕ → ℝ) (hR : ∀ n, 0 < R n) (hR1 : ∀ n, R n ≤ 1)
    (ha : ∀ n, 0 ≤ a n) (ha0 : Tendsto a atTop (𝓝 0))
    (herr : ∀ n, (∫ x in ball (0 : E) (R n), (q x)^2) ≤ (a n)^2*(R n)^8) :
    q = 0 := by
  obtain ⟨C,hC,hbound⟩ := actual_quadratic_scaled_L2_jet_bound_two
  have hb (n : ℕ) := hbound q hq (R n) (hR n) (a n) (ha n) (herr n)
  have hlim : Tendsto (fun n => C*a n) atTop (𝓝 0) := by
    simpa only [mul_zero] using ha0.const_mul C
  have h0 : |q 0| ≤ 0 := ge_of_tendsto' hlim (fun n =>
    (hb n).1.trans (mul_le_of_le_one_right (mul_nonneg hC.le (ha n))
      (by nlinarith [hR n,hR1 n] : (R n)^2 ≤ 1)))
  have h1 : ‖fderiv ℝ q 0‖ ≤ 0 := ge_of_tendsto' hlim (fun n =>
    (hb n).2.1.trans (mul_le_of_le_one_right (mul_nonneg hC.le (ha n)) (hR1 n)))
  have h2 : ‖realHessian q 0‖ ≤ 0 := ge_of_tendsto' hlim (fun n => (hb n).2.2)
  have hz0 : q 0 = 0 := abs_eq_zero.mp (le_antisymm h0 (abs_nonneg _))
  have hz1 : fderiv ℝ q 0 = 0 := norm_eq_zero.mp (le_antisymm h1 (norm_nonneg _))
  have hz2 : realHessian q 0 = 0 := by
    exact (ContinuousLinearMap.opNorm_zero_iff (realHessian q 0)).mp
      (le_antisymm h2 (norm_nonneg (realHessian q 0)))
  exact quadratic_zero_of_two_jet_zero hq 0 hz0 hz1 hz2

theorem actual_quadratic_L2_approximation_unique_two
    {u p q : E → ℝ} (hp : IsQuadraticPolynomial p) (hq : IsQuadraticPolynomial q)
    (R a : ℕ → ℝ) (hR : ∀ n, 0 < R n) (hR1 : ∀ n, R n ≤ 1)
    (ha : ∀ n, 0 ≤ a n) (ha0 : Tendsto a atTop (𝓝 0))
    (hu : ∀ n, MemLp u 2 (volume.restrict (ball (0 : E) (R n))))
    (hpE : ∀ n, (∫ x in ball (0 : E) (R n), (u x-p x)^2) ≤ (a n)^2*(R n)^8)
    (hqE : ∀ n, (∫ x in ball (0 : E) (R n), (u x-q x)^2) ≤ (a n)^2*(R n)^8) :
    p = q := by
  have hdiff : (fun x => p x-q x) = (0 : E → ℝ) := by
    apply actual_quadratic_zero_of_vanishing_scaled_L2_two (IsQuadraticPolynomial_sub hp hq)
      R (fun n => 2*a n) hR hR1 (fun n => mul_nonneg (by norm_num) (ha n))
      (by simpa only [mul_zero] using ha0.const_mul 2)
    intro n
    have hpm := actual_continuous_ball_memLp_two (IsQuadraticPolynomial_contDiff hp 0).continuous 0 (R n)
    have hqm := actual_continuous_ball_memLp_two (IsQuadraticPolynomial_contDiff hq 0).continuous 0 (R n)
    have hi := integral_mono_ae (hpm.sub hqm).integrable_sq
      (((hu n).sub hpm).integrable_sq.const_mul 2 |>.add
        (((hu n).sub hqm).integrable_sq.const_mul 2))
      (Filter.Eventually.of_forall (fun x => by
        change (p x-q x)^2 ≤ 2*(u x-p x)^2+2*(u x-q x)^2
        nlinarith [sq_nonneg ((u x-p x)+(u x-q x))]))
    simp only [Pi.add_apply,Pi.sub_apply] at hi
    have hip : Integrable (fun x => 2*(u x-p x)^2) (volume.restrict (ball (0 : E) (R n))) := by
      simpa only [Pi.sub_apply] using (((hu n).sub hpm).integrable_sq.const_mul 2)
    have hiq : Integrable (fun x => 2*(u x-q x)^2) (volume.restrict (ball (0 : E) (R n))) := by
      simpa only [Pi.sub_apply] using (((hu n).sub hqm).integrable_sq.const_mul 2)
    rw [integral_add hip hiq,integral_const_mul,integral_const_mul] at hi
    nlinarith [hpE n,hqE n]
  funext x
  have hh := congrFun hdiff x
  simpa only [Pi.zero_apply,sub_eq_zero] using hh

end PowerConvexity
