import PowerConvexity.Algebra.SchurSpectrum
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-! # A unit phase making a scalar congruence nonnegative -/
set_option autoImplicit false
namespace PowerConvexity

theorem exists_unit_phase_square (z : ℂ) :
    ∃ a : ℂ, Complex.normSq a = 1 ∧ a^2 * z = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · exact ⟨1, by norm_num, by simp [hz]⟩
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  let a : ℂ := (star z / (‖z‖ : ℂ)) ^ ((2 : ℂ)⁻¹)
  have ha : a^2 = star z / (‖z‖ : ℂ) :=
    Complex.cpow_nat_inv_pow _ (by norm_num : (2 : ℕ) ≠ 0)
  have han : ‖a‖^2 = 1 := by
    have h := congrArg norm ha
    simpa only [norm_pow, norm_div, norm_star, Complex.norm_real,
      Real.norm_eq_abs, abs_norm, div_self hn] using h
  refine ⟨a, (Complex.normSq_eq_norm_sq a).trans han, ?_⟩
  rw [ha, div_mul_eq_mul_div, Complex.star_def, Complex.conj_mul']
  push_cast
  field_simp

end PowerConvexity
