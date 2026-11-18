import PowerConvexity.Algebra.TraceRatioGradientAbsorption

/-! # Operator-norm versions of the ratio-gradient absorption estimates -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace PowerConvexity
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem weighted_diagonal_norm_bound {a b α β : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : 0 < a+b)
    (hα1 : 1 ≤ α) (hα2 : α ≤ 2) (hβ1 : 1 ≤ β) (hβ2 : β ≤ 2) (p q : V) :
    ‖p‖+‖q‖ ≤ 2*‖α • p+β • q‖+4*‖(a+b)⁻¹ • (b • p-a • q)‖ := by
  let H := a*α+b*β
  let G := α • p+β • q
  let R := (a+b)⁻¹ • (b • p-a • q)
  have hα : 0 ≤ α := by linarith
  have hβ : 0 ≤ β := by linarith
  have htH : a+b ≤ H := by
    dsimp only [H]
    nlinarith [mul_le_mul_of_nonneg_left hα1 ha,mul_le_mul_of_nonneg_left hβ1 hb]
  have hH : 0 < H := ht.trans_le htH
  have haH : a ≤ H := by linarith
  have hbH : b ≤ H := by linarith
  have hαH : α*(a+b) ≤ 2*H := by nlinarith [mul_le_mul_of_nonneg_right hα2 ht.le]
  have hβH : β*(a+b) ≤ 2*H := by nlinarith [mul_le_mul_of_nonneg_right hβ2 ht.le]
  have hR : (a+b) • R = b • p-a • q := by
    dsimp only [R]
    rw [smul_smul,mul_inv_cancel₀ ht.ne',one_smul]
  have hep : H • p = a • G+(β*(a+b)) • R := by
    calc
      H • p = a • G+β • (b • p-a • q) := by dsimp only [H,G]; module
      _ = _ := by rw [← hR,smul_smul]
  have heq : H • q = b • G-(α*(a+b)) • R := by
    calc
      H • q = b • G-α • (b • p-a • q) := by dsimp only [H,G]; module
      _ = _ := by rw [← hR,smul_smul]
  have hp : ‖p‖ ≤ ‖G‖+2*‖R‖ := by
    apply (mul_le_mul_iff_right₀ hH).mp
    calc
      H*‖p‖ = ‖H • p‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_pos hH]
      _ = ‖a • G+(β*(a+b)) • R‖ := congrArg norm hep
      _ ≤ ‖a • G‖+‖(β*(a+b)) • R‖ := norm_add_le _ _
      _ = a*‖G‖+(β*(a+b))*‖R‖ := by
        simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg ha,abs_of_nonneg (mul_nonneg hβ ht.le)]
      _ ≤ H*‖G‖+(2*H)*‖R‖ := by gcongr
      _ = _ := by ring
  have hq : ‖q‖ ≤ ‖G‖+2*‖R‖ := by
    apply (mul_le_mul_iff_right₀ hH).mp
    calc
      H*‖q‖ = ‖H • q‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_pos hH]
      _ = ‖b • G-(α*(a+b)) • R‖ := congrArg norm heq
      _ ≤ ‖b • G‖+‖(α*(a+b)) • R‖ := norm_sub_le _ _
      _ = b*‖G‖+(α*(a+b))*‖R‖ := by
        simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg hb,abs_of_nonneg (mul_nonneg hα ht.le)]
      _ ≤ H*‖G‖+(2*H)*‖R‖ := by gcongr
      _ = _ := by ring
  change ‖p‖+‖q‖ ≤ 2*‖G‖+4*‖R‖
  linarith

theorem weighted_diagonal_norm_bound_metric {a b α β K : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : 0 < a+b)
    (hα1 : 1 ≤ α) (hα2 : α ≤ 2) (hβ1 : 1 ≤ β) (hβ2 : β ≤ 2)
    (hK : 0 ≤ K) (p q x y : V) (hx : ‖x‖ ≤ K) (hy : ‖y‖ ≤ K) :
    ‖p‖+‖q‖ ≤ 2*‖α • (p-a • x)+β • (q-b • y)‖+
      4*K*(a+b)+4*‖(a+b)⁻¹ • (b • p-a • q)‖ := by
  have hα0 : 0 ≤ α := by linarith
  have hβ0 : 0 ≤ β := by linarith
  have herr : ‖(α*a) • x+(β*b) • y‖ ≤ 2*K*(a+b) := by
    calc
      _ ≤ ‖(α*a) • x‖+‖(β*b) • y‖ := norm_add_le _ _
      _ = (α*a)*‖x‖+(β*b)*‖y‖ := by
        simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hα0 ha),abs_of_nonneg (mul_nonneg hβ0 hb)]
      _ ≤ (2*a)*K+(2*b)*K := by gcongr
      _ = _ := by ring
  have hgrad : ‖α • p+β • q‖ ≤ ‖α • (p-a • x)+β • (q-b • y)‖+2*K*(a+b) := by
    have heq : α • p+β • q = (α • (p-a • x)+β • (q-b • y))+((α*a) • x+(β*b) • y) := by module
    rw [heq]
    exact (norm_add_le _ _).trans (add_le_add_right herr _)
  have hh := weighted_diagonal_norm_bound ha hb ht hα1 hα2 hβ1 hβ2 p q
  linarith

theorem linear_abs_le_elliptic_square {t κ : ℝ} (ht : 0 < t) (hk : 0 < κ) (A r : ℝ) :
    A*|r| ≤ κ/t*r^2+A^2*t/(4*κ) := by
  have hh := linear_abs_le_scaled_square (div_pos ht hk) A r
  calc
    A*|r| ≤ r^2/(t/κ)+A^2*(t/κ)/4 := hh
    _ = _ := by field_simp [ht.ne',hk.ne'] <;> ring

theorem norm_gradient_negative_square_absorption
    {t κ C0 C1 C2 P Q R r s G L : ℝ}
    (ht : 0 < t) (hk : 0 < κ) (hC : 0 ≤ C1)
    (hR : 0 ≤ R) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hgrad : P+Q ≤ 2*G+C2*t+4*R)
    (hL : L ≤ C0*t+C1*(P+Q+r+s)-κ/t*(R^2+r^2+s^2)) :
    L ≤ (C0+C1*C2+5*C1^2/κ)*t+2*C1*G := by
  have hd := mul_le_mul_of_nonneg_left hgrad hC
  have hRR := linear_abs_le_elliptic_square ht hk (4*C1) R
  have hrr := linear_abs_le_elliptic_square ht hk C1 r
  have hss := linear_abs_le_elliptic_square ht hk C1 s
  rw [abs_of_nonneg hR] at hRR
  rw [abs_of_nonneg hr] at hrr
  rw [abs_of_nonneg hs] at hss
  have hCt : 0 ≤ C1^2*t/κ := div_nonneg (mul_nonneg (sq_nonneg C1) ht.le) hk.le
  simp only [div_eq_mul_inv,mul_inv_rev] at hRR hrr hss hCt hL ⊢
  norm_num at hRR hrr hss
  nlinarith only [hd,hRR,hrr,hss,hCt,hL]

end PowerConvexity
