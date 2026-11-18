import PowerConvexity.Algebra.QuotientRatioSecondJetTwo
import PowerConvexity.Algebra.TraceRatioGradientAbsorption

/-! # Bounds for all variable-metric terms in the normalized quotient Hessian -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace PowerConvexity

theorem negative_shifted_square_bound {t B R delta : ℝ} (ht : 0 < t) (hB : 0 ≤ B)
    (hd : |delta| ≤ 2*B*t) :
    -2/t*(R-delta)^2 ≤ -1/t*R^2+8*B^2*t := by
  have hd2 : delta^2 ≤ (2*B*t)^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg delta) (by positivity : 0 ≤ 2*B*t)).mpr hd
  have hp : -2*(R-delta)^2 ≤ -R^2+8*B^2*t^2 := by
    nlinarith [sq_nonneg (R-2*delta)]
  calc
    -2/t*(R-delta)^2 = (-2*(R-delta)^2)/t := by ring
    _ ≤ (-R^2+8*B^2*t^2)/t := div_le_div_of_nonneg_right hp ht.le
    _ = _ := by field_simp [ht.ne'] <;> ring

theorem negative_metric_product_bound {a b B r z : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : 0 < a+b) (hB : 0 ≤ B) (hz : |z| ≤ B) :
    -2/(a+b)*((r-a*z)*(r-b*z)) ≤ -r^2/(a+b)+B^2*(a+b) := by
  have hz2 : z^2 ≤ B^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg z) hB).mpr hz
  have hq := mul_le_mul_of_nonneg_left hz2 (sq_nonneg (a+b))
  have hp : -2*((r-a*z)*(r-b*z)) ≤ -r^2+B^2*(a+b)^2 := by
    nlinarith [sq_nonneg (r-(a+b)*z),mul_nonneg (mul_nonneg ha hb) (sq_nonneg z)]
  calc
    -2/(a+b)*((r-a*z)*(r-b*z)) = (-2*((r-a*z)*(r-b*z)))/(a+b) := by ring
    _ ≤ (-r^2+B^2*(a+b)^2)/(a+b) := div_le_div_of_nonneg_right hp ht.le
    _ = _ := by field_simp [ht.ne'] <;> ring

theorem metric_diagonal_error_bound {α a p x z w X B : ℝ}
    (hα0 : 0 ≤ α) (hα2 : α ≤ 2) (ha : 0 ≤ a) (hB : 0 ≤ B)
    (hx : |x| ≤ B) (hz : |z| ≤ B) (hw : |w| ≤ B) (hX : |X| ≤ B) :
    α*(-2*p*x+2*a*(x^2+z^2+w^2)-a*X) ≤
      4*B*|p|+(12*B^2+2*B)*a := by
  have hsq (y : ℝ) (hy : |y| ≤ B) : y^2 ≤ B^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg y) hB).mpr hy
  have hpx : -p*x ≤ |p| *B := by
    calc
      _ ≤ |p*x| := by simpa only [neg_mul] using neg_le_abs (p*x)
      _ = |p| *|x| := abs_mul _ _
      _ ≤ |p| *B := mul_le_mul_of_nonneg_left hx (abs_nonneg p)
  have hlin : α*(-2*p*x) ≤ 4*B*|p| := by
    have h1 := mul_le_mul_of_nonneg_left hpx (show 0 ≤ 2*α by positivity)
    have h2 := mul_le_mul_of_nonneg_right hα2 (show 0 ≤ 2*|p| *B by positivity)
    nlinarith only [h1,h2]
  have hquad : α*(2*a*(x^2+z^2+w^2)) ≤ 12*B^2*a := by
    calc
      _ ≤ 2*(2*a*(3*B^2)) := by
        gcongr
        nlinarith [hsq x hx,hsq z hz,hsq w hw]
      _ = _ := by ring
  have hX' : -X ≤ B := (neg_le_abs X).trans hX
  have hzero : α*(-a*X) ≤ 2*B*a := by
    have h1 := mul_le_mul_of_nonneg_left hX' (mul_nonneg hα0 ha)
    have h2 := mul_le_mul_of_nonneg_right hα2 (mul_nonneg ha hB)
    nlinarith only [h1,h2]
  nlinarith only [hlin,hquad,hzero]

theorem metric_cross_error_bound {α β r s z w B : ℝ}
    (hα0 : 0 ≤ α) (hα2 : α ≤ 2) (hβ0 : 0 ≤ β) (hβ2 : β ≤ 2)
    (hB : 0 ≤ B) (hz : |z| ≤ B) (hw : |w| ≤ B) :
    -2*(α+β)*(r*z+s*w) ≤ 8*B*(|r|+|s|) := by
  have hlin : -(r*z+s*w) ≤ B*(|r|+|s|) := by
    calc
      _ ≤ |r*z+s*w| := neg_le_abs _
      _ ≤ |r*z|+|s*w| := abs_add_le _ _
      _ = |r| *|z|+|s| *|w| := by rw [abs_mul,abs_mul]
      _ ≤ |r| *B+|s| *B := by gcongr
      _ = _ := by ring
  have hh := mul_le_mul_of_nonneg_left hlin (show 0 ≤ 2*(α+β) by positivity)
  have hc : α+β ≤ 4 := by linarith
  have hh2 := mul_le_mul_of_nonneg_right hc (show 0 ≤ 2*B*(|r|+|s|) by positivity)
  nlinarith only [hh,hh2]

theorem normalized_quotient_metric_error_bound
    {a b α β p q r s x y z w U V X Y R delta B : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : 0 < a+b)
    (hα0 : 0 ≤ α) (hα2 : α ≤ 2) (hβ0 : 0 ≤ β) (hβ2 : β ≤ 2)
    (hB : 0 ≤ B) (hx : |x| ≤ B) (hy : |y| ≤ B)
    (hz : |z| ≤ B) (hw : |w| ≤ B) (hX : |X| ≤ B) (hY : |Y| ≤ B)
    (hd : |delta| ≤ 2*B*(a+b)) :
    α*(U-2*p*x-2*(r*z+s*w)+2*a*(x^2+z^2+w^2)-a*X)+
      β*(V-2*q*y-2*(r*z+s*w)+2*b*(y^2+z^2+w^2)-b*Y)-
      2/(a+b)*((R-delta)^2+(r-a*z)*(r-b*z)+(s-a*w)*(s-b*w)) ≤
    α*U+β*V+(2*B+22*B^2)*(a+b)+8*B*(|p|+|q|+|r|+|s|)-
      1/(a+b)*(R^2+r^2+s^2) := by
  have hp := metric_diagonal_error_bound hα0 hα2 ha hB hx hz hw hX (p := p)
  have hq := metric_diagonal_error_bound hβ0 hβ2 hb hB hy hz hw hY (p := q)
  have hcross := metric_cross_error_bound hα0 hα2 hβ0 hβ2 hB hz hw (r := r) (s := s)
  have hR := negative_shifted_square_bound ht hB hd (R := R)
  have hr := negative_metric_product_bound ha hb ht hB hz (r := r)
  have hs := negative_metric_product_bound ha hb ht hB hw (r := s)
  have hrest : 0 ≤ 4*B*(|p|+|q|) := by positivity
  simp only [div_eq_mul_inv] at hR hr hs ⊢
  nlinarith only [hp,hq,hcross,hR,hr,hs,hrest]

end PowerConvexity
