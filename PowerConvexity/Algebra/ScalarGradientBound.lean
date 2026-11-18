import PowerConvexity.Algebra.ScalarSigmaIdentity

/-! # Explicit gradient bound obtained from the exact scalar equation -/

set_option autoImplicit false

namespace PowerConvexity

theorem scalar_gradient_bound {h α σ R t : ℝ} {s g q : ℂ}
    (hh : 0 ≤ h) (hα : 0 ≤ α) (hσ : 0 ≤ σ) (hR : 0 < R)
    (heq : R * t = -Complex.normSq s - 4 * h * (s * g * star q).re -
      2 * h * α * σ * R^2 - 2 * h^2 * σ * (3 + σ) * R * Complex.normSq g) :
    t ≤ (4 * h * ‖g‖ * ‖q‖ / R) * ‖s‖ := by
  have hre : -(s * g * star q).re ≤ ‖s‖ * ‖g‖ * ‖q‖ := by
    have h := (abs_le.mp (Complex.abs_re_le_norm (s * g * star q))).1
    simp only [norm_mul, norm_star] at h
    linarith
  have hcross := mul_le_mul_of_nonneg_left hre (show 0 ≤ 4 * h by positivity)
  have h1 : 0 ≤ 2 * h * α * σ * R^2 := by positivity
  have hgnonneg := Complex.normSq_nonneg g
  have h2 : 0 ≤ 2 * h^2 * σ * (3 + σ) * R * Complex.normSq g := by positivity
  have ht : R * t ≤ 4 * h * ‖g‖ * ‖q‖ * ‖s‖ := by
    nlinarith [Complex.normSq_nonneg s]
  calc
    t = (R * t) / R := by field_simp
    _ ≤ (4 * h * ‖g‖ * ‖q‖ * ‖s‖) / R :=
      div_le_div_of_nonneg_right ht hR.le
    _ = (4 * h * ‖g‖ * ‖q‖ / R) * ‖s‖ := by ring

end PowerConvexity
