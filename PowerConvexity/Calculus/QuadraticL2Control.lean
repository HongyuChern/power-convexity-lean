import PowerConvexity.Calculus.QuadraticRobustness
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Genuine L2 control of the centered holomorphic-square tests -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ContDiff
namespace PowerConvexity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

noncomputable def quadraticL2Energy (μ : Measure E) (K : Set E) (q : E → ℝ) : ℝ :=
  ∫ y in K, (q y)^2 ∂μ

theorem quadraticL2Energy_nonneg (μ : Measure E) (K : Set E) (q : E → ℝ) :
    0 ≤ quadraticL2Energy μ K q := integral_nonneg fun y => sq_nonneg _

theorem realPartSquare_L2_bound (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
    {K : Set E} (hK : IsCompact K) (ell : E →L[ℝ] ℂ) (c : E)
    {R : ℝ} (hR : 0 ≤ R) (hbound : ∀ y ∈ K, ‖y-c‖ ≤ R) (δ : ℝ) :
    quadraticL2Energy μ K (fun y => -δ * realPartSquare ell c y) ≤
      δ^2 * ‖ell‖^4 * R^4 * μ.real K := by
  have hpt (y : E) (hy : y ∈ K) :
      (-δ * realPartSquare ell c y)^2 ≤ δ^2 * ‖ell‖^4 * R^4 := by
    have hq := abs_realPartSquare_le ell c y
    have hr := pow_le_pow_left₀ (norm_nonneg (y-c)) (hbound y hy) 2
    have hqR : |realPartSquare ell c y| ≤ ‖ell‖^2 * R^2 :=
      hq.trans (mul_le_mul_of_nonneg_left hr (sq_nonneg _))
    have hs := pow_le_pow_left₀ (abs_nonneg (realPartSquare ell c y)) hqR 2
    rw [sq_abs] at hs
    have hm := mul_le_mul_of_nonneg_left hs (sq_nonneg δ)
    nlinarith [hm]
  have hqi : IntegrableOn (fun y => (-δ * realPartSquare ell c y)^2) K μ :=
    ((continuous_const.mul (realPartSquare_contDiff ell c 0).continuous).pow 2).continuousOn.integrableOn_compact hK
  have hci : IntegrableOn (fun _ : E => δ^2 * ‖ell‖^4 * R^4) K μ :=
    continuousOn_const.integrableOn_compact hK
  have h := setIntegral_mono_on hqi hci hK.measurableSet hpt
  simpa only [quadraticL2Energy, setIntegral_const, smul_eq_mul, mul_comm] using h

/-- A positive radius for all unit-norm holomorphic-square tests, with the
same real L2 energy convention as the frozen manuscript. -/
theorem exists_square_test_L2_radius (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
    {K : Set E} (hK : IsCompact K) (c : E) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ell : E →L[ℝ] ℂ, ‖ell‖ = 1 →
      quadraticL2Energy μ K (fun y => -δ * realPartSquare ell c y) ≤ ε := by
  obtain ⟨R, hR, hbound⟩ := hK.isBounded.exists_pos_norm_le
  let S : ℝ := R + ‖c‖
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hb (y : E) (hy : y ∈ K) : ‖y-c‖ ≤ S := by
    dsimp [S]
    linarith [norm_sub_le y c, hbound y hy]
  let D : ℝ := S^4 * μ.real K
  have hD : 0 ≤ D := mul_nonneg (pow_nonneg hS _) (measureReal_nonneg)
  let δ : ℝ := min 1 (ε / (D+1))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε (by linarith))
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδD : δ * (D+1) ≤ ε := by
    exact (le_div_iff₀ (by linarith : 0 < D+1)).mp (min_le_right _ _)
  refine ⟨δ, hδ, ?_⟩
  intro ell hell
  have hbnd := realPartSquare_L2_bound μ hK ell c hS hb δ
  simp only [hell, one_pow, mul_one] at hbnd
  have hs : δ^2 ≤ δ := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hs hD
  have hfinal : δ^2 * D ≤ ε := by nlinarith
  exact hbnd.trans (by simpa only [D, mul_assoc] using hfinal)

end PowerConvexity
