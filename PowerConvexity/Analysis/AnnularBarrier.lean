import PowerConvexity.Analysis.GradientComparison
import PowerConvexity.Calculus.GaussianBarrier

/-! # The exponential annular barrier for a uniformly elliptic contraction -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff Topology

namespace PowerConvexity
open CHS.Calculus

theorem exists_annular_barrier_exponent {ell Λ C R : ℝ}
    (hell : 0 < ell) (hΛ : 0 ≤ Λ) (hC : 0 ≤ C) (hR : 0 < R) :
    ∃ k : ℝ, 0 < k ∧ 2 * k * Λ + C * (1 + 2 * k * R) < k^2 * ell * R^2 := by
  let D := ell * R^2
  let A := 2 * Λ + 2 * C * R + C + 1
  have hD : 0 < D := by dsimp [D]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  let k := A / D + 1
  have hk : 1 < k := by
    have hd : 0 < A / D := div_pos hA hD
    dsimp only [k]
    linarith
  have hkD : k * D = A + D := by dsimp [k]; field_simp
  have hlarge : A < k * D := by linarith
  have hmul := mul_lt_mul_of_pos_left hlarge (show 0 < k by linarith)
  refine ⟨k, by linarith, ?_⟩
  dsimp only [A, D] at hmul
  nlinarith [mul_nonneg hC (show 0 ≤ k - 1 by linarith)]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The radial and trace bounds are the two explicit uniform ellipticity data
used by this barrier; positivity on arbitrary Hessians is used by comparison. -/
theorem annularBarrier_strict_subsolution
    (L : (E →L[ℝ] E →L[ℝ] ℝ) →ₗ[ℝ] ℝ) (c x : E)
    {ell Λ C R k : ℝ} (hell : 0 < ell) (hC : 0 ≤ C) (hR : 0 < R) (hk : 0 < k)
    (hchoice : 2 * k * Λ + C * (1 + 2 * k * R) < k^2 * ell * R^2)
    (hlower : ell * ‖x-c‖^2 ≤ L (realRankOneForm (x-c)))
    (htrace : L (realInnerForm (E := E)) ≤ Λ)
    (hrlow : R / 2 ≤ ‖x-c‖) (hrhigh : ‖x-c‖ ≤ R) :
    C * (annularBarrier k R c x + ‖fderiv ℝ (annularBarrier k R c) x‖) <
      L (realHessian (annularBarrier k R c) x) := by
  have hG : 0 < radialGaussian k c x := Real.exp_pos _
  have hlow2 : R^2 ≤ 4 * ‖x-c‖^2 := by nlinarith [norm_nonneg (x-c)]
  have hfirst : k^2 * ell * R^2 ≤ 4 * k^2 * L (realRankOneForm (x-c)) := by
    have h1 := mul_le_mul_of_nonneg_left hlow2 (show 0 ≤ k^2 * ell by positivity)
    have h2 := mul_le_mul_of_nonneg_left hlower (show 0 ≤ 4 * k^2 by positivity)
    nlinarith
  have htrace' := mul_le_mul_of_nonneg_left htrace (show 0 ≤ 2 * k by positivity)
  have hnorm : 2 * k * ‖x-c‖ ≤ 2 * k * R :=
    mul_le_mul_of_nonneg_left hrhigh (by positivity)
  have hcoef : C * (1 + 2 * k * ‖x-c‖) <
      4 * k^2 * L (realRankOneForm (x-c)) - 2 * k * L (realInnerForm (E := E)) := by
    have hCnorm := mul_le_mul_of_nonneg_left hnorm hC
    linarith
  have hstrict := mul_lt_mul_of_pos_left hcoef hG
  have hvle := annularBarrier_le_gaussian k R c x
  have hsmall := mul_le_mul_of_nonneg_left hvle hC
  rw [norm_fderiv_annularBarrier hk.le, realHessian_annularBarrier,
    map_sub L _ _, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  nlinarith

end PowerConvexity
