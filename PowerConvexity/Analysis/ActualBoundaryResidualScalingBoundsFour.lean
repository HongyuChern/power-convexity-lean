import PowerConvexity.Analysis.ActualCenteredScalarCoeffFour

/-! # Quantitative bounds at the actual distance scale, with every exponent checked -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_boundary_scale_exponent_bound_four {r alpha gamma : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hga : gamma ≤ alpha) :
    (r^gamma)⁻¹*r^alpha ≤ 1 := by
  rw [inv_mul_eq_div]
  exact (div_le_one (Real.rpow_pos_of_pos hr gamma)).mpr
    (Real.rpow_le_rpow_of_exponent_ge hr hr1 hga)

theorem actual_boundary_scaled_source_growth_four {r alpha gamma K d : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (halpha : 0 ≤ alpha) (hga : gamma ≤ alpha)
    (hK : 0 ≤ K) (hd : 0 ≤ d) (hd6 : d ≤ 6*r) :
    (r^gamma)⁻¹*(K*d^alpha) ≤ K*(6 : ℝ)^alpha := by
  have hpow := actual_boundary_scale_exponent_bound_four hr hr1 hga
  calc
    _ ≤ (r^gamma)⁻¹*(K*(6*r)^alpha) := by gcongr
    _ = K*(6 : ℝ)^alpha*((r^gamma)⁻¹*r^alpha) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 6) hr.le]
      ring
    _ ≤ K*(6 : ℝ)^alpha*1 := mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = _ := mul_one _

theorem actual_boundary_scaled_remainder_bound_four {r gamma M d : ℝ}
    (hr : 0 < r) (hgamma : 0 ≤ gamma) (hM : 0 ≤ M) (hd : 0 ≤ d) (hd6 : d ≤ 6*r) :
    ((r^gamma)⁻¹*(r^2)⁻¹)*(M*d^2*d^gamma) ≤ 36*(6 : ℝ)^gamma*M := by
  calc
    _ ≤ ((r^gamma)⁻¹*(r^2)⁻¹)*(M*(6*r)^2*(6*r)^gamma) := by gcongr
    _ = _ := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 6) hr.le]
      field_simp [ne_of_gt (Real.rpow_pos_of_pos hr gamma)]
      <;> ring

theorem actual_boundary_actual_residual_bound_four {N c x : E} {u q : E → ℝ}
    {R r gamma M : ℝ} (hr : 0 < r) (hgamma : 0 ≤ gamma) (hM : 0 ≤ M)
    (hsmall : 6*r < R/2)
    (herr : ∀ y : E, 0 ≤ inner ℝ N y → ‖y-c‖ < R/2 →
      |u y-q y| ≤ M*‖y-c‖^2*‖y-c‖^gamma)
    (hmap : ∀ z ∈ ball (0 : E) 2, 0 ≤ inner ℝ N (x+r • z))
    (hnear : ∀ z ∈ ball (0 : E) 2, ‖(x+r • z)-c‖ ≤ 6*r) :
    ∀ z ∈ ball (0 : E) 2,
      |actualCenteredResidualFour x r (r^gamma) u q z| ≤ 36*(6 : ℝ)^gamma*M := by
  intro z hz
  have hp := Real.rpow_pos_of_pos hr gamma
  have hh := herr _ (hmap z hz) ((hnear z hz).trans_lt hsmall)
  simp only [actualCenteredResidualFour,abs_mul,abs_of_pos (inv_pos.mpr hp),
    abs_of_pos (inv_pos.mpr (sq_pos_of_pos hr))]
  exact (mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ (r^gamma)⁻¹*(r^2)⁻¹)).trans
    (actual_boundary_scaled_remainder_bound_four hr hgamma hM (norm_nonneg _) (hnear z hz))

end PowerConvexity
