import PowerConvexity.Algebra.UniformBoundaryHessian

/-! # Actual continuous bilinear norm from homogeneous quadratic bounds. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Topology
namespace PowerConvexity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem bilinear_quadratic_upper_from_unit_bound
    (H : E →L[ℝ] E →L[ℝ] ℝ) {M : ℝ}
    (hunit : ∀ v : E, ‖v‖ = 1 → H v v ≤ M) :
    ∀ v : E, H v v ≤ M*‖v‖^2 := by
  intro v
  by_cases hv : v = 0
  · subst v
    simp
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let z : E := ‖v‖⁻¹ • v
  have hz : ‖z‖ = 1 := by
    rw [show z = ‖v‖⁻¹ • v from rfl,norm_smul,Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hn),inv_mul_cancel₀ hn.ne']
  have hsplit : v = ‖v‖ • z := by
    dsimp only [z]
    rw [smul_smul,mul_inv_cancel₀ hn.ne',one_smul]
  calc
    H v v = ‖v‖^2*H z z := by
      conv_lhs => rw [hsplit]
      simp only [map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul]
      ring
    _ ≤ ‖v‖^2*M := mul_le_mul_of_nonneg_left (hunit z hz) (sq_nonneg _)
    _ = M*‖v‖^2 := mul_comm _ _

theorem symmetric_bilinear_norm_le_of_quadratic_abs_bound
    (H : E →L[ℝ] E →L[ℝ] ℝ) (hsym : ∀ v z : E, H v z = H z v)
    {M : ℝ} (hM : 0 ≤ M) (hquad : ∀ v : E, |H v v| ≤ M*‖v‖^2) :
    ‖H‖ ≤ 2*M := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro v hv
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro z hz
  rw [Real.norm_eq_abs]
  have hnp : ‖v+z‖ ≤ 2 := (norm_add_le _ _).trans (by rw [hv,hz]; norm_num)
  have hnm : ‖v-z‖ ≤ 2 := (norm_sub_le _ _).trans (by rw [hv,hz]; norm_num)
  have hnp2 : ‖v+z‖^2 ≤ 4 := by nlinarith [norm_nonneg (v+z)]
  have hnm2 : ‖v-z‖^2 ≤ 4 := by nlinarith [norm_nonneg (v-z)]
  have hp : |H (v+z) (v+z)| ≤ 4*M := (hquad _).trans (by nlinarith [mul_le_mul_of_nonneg_left hnp2 hM])
  have hm : |H (v-z) (v-z)| ≤ 4*M := (hquad _).trans (by nlinarith [mul_le_mul_of_nonneg_left hnm2 hM])
  have he : H (v+z) (v+z)-H (v-z) (v-z) = 4*H v z := by
    simp only [map_add,map_sub,ContinuousLinearMap.add_apply,ContinuousLinearMap.sub_apply,hsym z v]
    ring
  obtain ⟨hp1,hp2⟩ := abs_le.mp hp
  obtain ⟨hm1,hm2⟩ := abs_le.mp hm
  exact abs_le.mpr ⟨by linarith,by linarith⟩

end PowerConvexity
