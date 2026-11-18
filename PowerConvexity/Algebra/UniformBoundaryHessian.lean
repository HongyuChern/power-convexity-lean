import PowerConvexity.Calculus.BoundaryQuadraticSubsolutionEstimateTwo

/-! # Quantitative real bilinear assembly at a boundary hyperplane

These are elementary symmetric-bilinear estimates. The geometric and PDE
hypotheses supplying the tangent, mixed, and normal bounds are kept separate.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace PowerConvexity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem abs_bilinear_on_kernel_of_quadratic_bounds
    (H : E →L[ℝ] E →L[ℝ] ℝ) (D : E →L[ℝ] ℝ)
    (hsym : ∀ v z : E, H v z = H z v) {C : ℝ} (hC : 0 ≤ C)
    (hpos : ∀ v : E, D v = 0 → 0 ≤ H v v)
    (hupper : ∀ v : E, D v = 0 → H v v ≤ C*‖v‖^2)
    (v z : E) (hv : D v = 0) (hz : D z = 0) (hnv : ‖v‖ ≤ 1) (hnz : ‖z‖ ≤ 1) :
    |H v z| ≤ C := by
  have hp : D (v+z) = 0 := by rw [map_add,hv,hz,add_zero]
  have hm : D (v-z) = 0 := by rw [map_sub,hv,hz,sub_self]
  have hnp : ‖v+z‖ ≤ 2 := (norm_add_le _ _).trans (by linarith)
  have hnm : ‖v-z‖ ≤ 2 := (norm_sub_le _ _).trans (by linarith)
  have hnp2 : ‖v+z‖^2 ≤ 4 := by nlinarith [norm_nonneg (v+z)]
  have hnm2 : ‖v-z‖^2 ≤ 4 := by nlinarith [norm_nonneg (v-z)]
  have hP : H (v+z) (v+z) ≤ 4*C := by
    have hh := mul_le_mul_of_nonneg_left hnp2 hC
    nlinarith only [hupper (v+z) hp,hh]
  have hM : H (v-z) (v-z) ≤ 4*C := by
    have hh := mul_le_mul_of_nonneg_left hnm2 hC
    nlinarith only [hupper (v-z) hm,hh]
  have he : H (v+z) (v+z)-H (v-z) (v-z) = 4*H v z := by
    simp only [map_add,map_sub,ContinuousLinearMap.add_apply,ContinuousLinearMap.sub_apply,hsym z v]
    ring
  exact abs_le.mpr ⟨by nlinarith only [he,hP,hM,hpos (v+z) hp,hpos (v-z) hm],
    by nlinarith only [he,hP,hM,hpos (v+z) hp,hpos (v-z) hm]⟩

theorem linear_kernel_bound_from_unit_bound
    (L D : E →L[ℝ] ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hunit : ∀ v : E, D v = 0 → ‖v‖ ≤ 1 → |L v| ≤ M)
    (v : E) (hv : D v = 0) : |L v| ≤ M*‖v‖ := by
  by_cases hz : v = 0
  · subst v
    simp
  · have hn : 0 < ‖v‖ := norm_pos_iff.mpr hz
    have ht : D (‖v‖⁻¹ • v) = 0 := by rw [map_smul,hv,smul_zero]
    have hnt : ‖‖v‖⁻¹ • v‖ ≤ 1 := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn),inv_mul_cancel₀ hn.ne']
    have hh := hunit (‖v‖⁻¹ • v) ht hnt
    rw [map_smul,smul_eq_mul,abs_mul,abs_of_pos (inv_pos.mpr hn)] at hh
    have hh' : |L v|/‖v‖ ≤ M := by simpa only [div_eq_mul_inv,mul_comm] using hh
    exact (div_le_iff₀ hn).mp hh'

theorem quadratic_upper_from_unit_normal_tangent_bounds
    (H : E →L[ℝ] E →L[ℝ] ℝ) (D : E →L[ℝ] ℝ) (n : E)
    (hsym : ∀ v z : E, H v z = H z v) (hn : ‖n‖ = 1)
    (hD : ∀ v : E, D v = inner ℝ n v) {C M A : ℝ}
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hA : 0 ≤ A)
    (htan : ∀ v : E, D v = 0 → H v v ≤ C*‖v‖^2)
    (hmixed : ∀ v : E, D v = 0 → ‖v‖ ≤ 1 → |H n v| ≤ M)
    (hnormal : H n n ≤ A) (v : E) :
    H v v ≤ (4*C+4*M+A)*‖v‖^2 := by
  let a : ℝ := inner ℝ n v
  let p : E := v-a • n
  have hnn : inner ℝ n n = 1 := by rw [real_inner_self_eq_norm_sq,hn]; norm_num
  have hpt : D p = 0 := by
    rw [hD]
    dsimp only [p]
    rw [inner_sub_right,real_inner_smul_right,hnn,mul_one]
    exact sub_self _
  have ha : |a| ≤ ‖v‖ := by
    simpa only [a,Real.norm_eq_abs,hn,one_mul] using norm_inner_le_norm (𝕜 := ℝ) n v
  have hp : ‖p‖ ≤ 2*‖v‖ := by
    have hh := norm_sub_le v (a • n)
    rw [norm_smul,Real.norm_eq_abs,hn,mul_one] at hh
    change ‖p‖ ≤ _
    nlinarith only [hh,ha]
  have hp2 : ‖p‖^2 ≤ 4*‖v‖^2 := by
    have hh := (sq_le_sq₀ (norm_nonneg p) (by positivity : 0 ≤ 2*‖v‖)).mpr hp
    nlinarith only [hh]
  have ha2 : a^2 ≤ ‖v‖^2 := by
    have hh := (sq_le_sq₀ (abs_nonneg a) (norm_nonneg v)).mpr ha
    simpa only [sq_abs] using hh
  have ht : H p p ≤ 4*C*‖v‖^2 := by
    have hh := mul_le_mul_of_nonneg_left hp2 hC
    nlinarith only [htan p hpt,hh]
  have hm : |H n p| ≤ 2*M*‖v‖ := by
    have hh := linear_kernel_bound_from_unit_bound (H n) D hM hmixed p hpt
    have hh' := mul_le_mul_of_nonneg_left hp hM
    nlinarith only [hh,hh']
  have hcross : 2*a*H n p ≤ 4*M*‖v‖^2 := by
    have hh := mul_le_mul ha hm (abs_nonneg _) (norm_nonneg v)
    have haH := le_abs_self (a*H n p)
    rw [abs_mul] at haH
    nlinarith only [hh,haH]
  have hnnA : a^2*H n n ≤ A*‖v‖^2 := by
    have hh := mul_le_mul_of_nonneg_left hnormal (sq_nonneg a)
    have hh' := mul_le_mul_of_nonneg_right ha2 hA
    nlinarith only [hh,hh']
  have hsplit : v = p+a • n := by dsimp [p]; module
  have he : H v v = H p p+2*a*H n p+a^2*H n n := by
    conv_lhs => rw [hsplit]
    simp only [map_add,map_smul,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
    rw [hsym p n]
    ring
  rw [he]
  nlinarith only [ht,hcross,hnnA]

end PowerConvexity
