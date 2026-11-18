import PowerConvexity.Algebra.TraceDetRatioTwo

/-! # Absorbing full matrix derivatives by the negative ratio-Hessian squares -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace PowerConvexity

theorem weighted_diagonal_gradient_bound {a b α β : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : 0 < a+b)
    (hα1 : 1 ≤ α) (hα2 : α ≤ 2) (hβ1 : 1 ≤ β) (hβ2 : β ≤ 2)
    (p q : ℝ) :
    |p|+|q| ≤ 2*|α*p+β*q|+4*|(b*p-a*q)/(a+b)| := by
  let H := a*α+b*β
  let G := α*p+β*q
  let R := (b*p-a*q)/(a+b)
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
  have hep : H*p = a*G+β*(a+b)*R := by
    dsimp only [H,G,R]
    field_simp [ht.ne']
    <;> ring
  have heq : H*q = b*G-α*(a+b)*R := by
    dsimp only [H,G,R]
    field_simp [ht.ne']
    <;> ring
  have hp : |p| ≤ |G|+2*|R| := by
    apply (mul_le_mul_iff_right₀ hH).mp
    calc
      H*|p| = |H*p| := by rw [abs_mul,abs_of_pos hH]
      _ = |a*G+β*(a+b)*R| := congrArg abs hep
      _ ≤ |a*G|+|β*(a+b)*R| := abs_add_le _ _
      _ = a*|G|+(β*(a+b))*|R| := by rw [abs_mul,abs_mul,abs_of_nonneg ha,abs_of_nonneg (mul_nonneg hβ ht.le)]
      _ ≤ H*|G|+(2*H)*|R| := by gcongr
      _ = H*(|G|+2*|R|) := by ring
  have hq : |q| ≤ |G|+2*|R| := by
    apply (mul_le_mul_iff_right₀ hH).mp
    calc
      H*|q| = |H*q| := by rw [abs_mul,abs_of_pos hH]
      _ = |b*G-α*(a+b)*R| := congrArg abs heq
      _ ≤ |b*G|+|α*(a+b)*R| := abs_sub _ _
      _ = b*|G|+(α*(a+b))*|R| := by rw [abs_mul,abs_mul,abs_of_nonneg hb,abs_of_nonneg (mul_nonneg hα ht.le)]
      _ ≤ H*|G|+(2*H)*|R| := by gcongr
      _ = H*(|G|+2*|R|) := by ring
  change |p|+|q| ≤ 2*|G|+4*|R|
  linarith

theorem linear_abs_le_scaled_square {t : ℝ} (ht : 0 < t) (A r : ℝ) :
    A*|r| ≤ r^2/t+A^2*t/4 := by
  apply (mul_le_mul_iff_left₀ ht).mp
  rw [add_mul,div_mul_cancel₀ _ ht.ne']
  nlinarith [sq_nonneg (2*|r|-A*t),sq_abs r]

theorem trace_ratio_negative_square_absorption {t C p q r s R G L : ℝ}
    (ht : 0 < t) (hC : 0 ≤ C)
    (hgrad : |p|+|q| ≤ 2*|G|+4*|R|)
    (hL : L ≤ C*(t+|p|+|q|+|r|+|s|)-1/t*(R^2+r^2+s^2)) :
    L ≤ (C+5*C^2)*t+2*C*|G| := by
  have hd := mul_le_mul_of_nonneg_left hgrad hC
  have hR := linear_abs_le_scaled_square ht (4*C) R
  have hr := linear_abs_le_scaled_square ht C r
  have hs := linear_abs_le_scaled_square ht C s
  have hQ : 0 ≤ (R^2+r^2+s^2)/t := by positivity
  have hCt : 0 ≤ C^2*t := mul_nonneg (sq_nonneg C) ht.le
  simp only [div_eq_mul_inv] at hL hR hr hs hQ
  nlinarith only [hd,hR,hr,hs,hQ,hCt,hL]

end PowerConvexity
