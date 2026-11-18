import PowerConvexity.Calculus.HermitianQuotientRatioHessianTwo
import PowerConvexity.Algebra.QuotientRatioMetricErrorBoundsTwo

/-! # Actual directional Hessian estimate retaining the three negative squares -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open scoped ContDiff
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hermitianQuotientRatioFieldTwo_direction_bound
    {a b c d A B C D : E → ℝ} {x : E}
    (ha : ContDiffAt ℝ 2 a x) (hb : ContDiffAt ℝ 2 b x)
    (hc : ContDiffAt ℝ 2 c x) (hd : ContDiffAt ℝ 2 d x)
    (hA : ContDiffAt ℝ 2 A x) (hB : ContDiffAt ℝ 2 B x)
    (hC : ContDiffAt ℝ 2 C x) (hD : ContDiffAt ℝ 2 D x)
    (hc0 : c x = 0) (hd0 : d x = 0) (hA1 : A x = 1) (hB1 : B x = 1)
    (hC0 : C x = 0) (hD0 : D x = 0)
    (ha0 : 0 ≤ a x) (hb0 : 0 ≤ b x) (ht : 0 < a x+b x) (v : E)
    {K : ℝ} (hK : 0 ≤ K)
    (hDA : |fderiv ℝ A x v| ≤ K) (hDB : |fderiv ℝ B x v| ≤ K)
    (hDC : |fderiv ℝ C x v| ≤ K) (hDD : |fderiv ℝ D x v| ≤ K)
    (hHA : |realHessian A x v v| ≤ K) (hHB : |realHessian B x v v| ≤ K) :
    realHessian (hermitianQuotientRatioFieldTwo a b c d A B C D) x v v ≤
      (1+(b x)^2/(a x+b x)^2)*realHessian a x v v+
      (1+(a x)^2/(a x+b x)^2)*realHessian b x v v+
      (2*K+22*K^2)*(a x+b x)+
      8*K*(|fderiv ℝ a x v|+|fderiv ℝ b x v|+|fderiv ℝ c x v|+|fderiv ℝ d x v|)-
      1/(a x+b x)*(((b x*fderiv ℝ a x v-a x*fderiv ℝ b x v)/(a x+b x))^2+
        (fderiv ℝ c x v)^2+(fderiv ℝ d x v)^2) := by
  have hab : 0 ≤ a x*b x := mul_nonneg ha0 hb0
  have habq : 0 ≤ a x*b x/(a x+b x) := div_nonneg hab ht.le
  have habt : a x*b x/(a x+b x) ≤ a x+b x := by
    rw [div_le_iff₀ ht]
    nlinarith [sq_nonneg (a x),sq_nonneg (b x)]
  have hdelta : |a x*b x*(fderiv ℝ A x v-fderiv ℝ B x v)/(a x+b x)| ≤
      2*K*(a x+b x) := by
    rw [show a x*b x*(fderiv ℝ A x v-fderiv ℝ B x v)/(a x+b x) =
      (a x*b x/(a x+b x))*(fderiv ℝ A x v-fderiv ℝ B x v) by ring,
      abs_mul,abs_of_nonneg habq]
    calc
      _ ≤ (a x+b x)*(|fderiv ℝ A x v|+|fderiv ℝ B x v|) := by
        gcongr
        exact abs_sub _ _
      _ ≤ (a x+b x)*(K+K) := by gcongr
      _ = _ := by ring
  obtain ⟨hα,hβ⟩ := traceDetRatioTwo_first_coeff_bounds ha0 hb0 ht
  have hbound := normalized_quotient_metric_error_bound ha0 hb0 ht
    (by linarith [hα.1] : 0 ≤ 1+(b x)^2/(a x+b x)^2) hα.2
    (by linarith [hβ.1] : 0 ≤ 1+(a x)^2/(a x+b x)^2) hβ.2
    hK hDA hDB hDC hDD hHA hHB hdelta
    (p := fderiv ℝ a x v) (q := fderiv ℝ b x v)
    (r := fderiv ℝ c x v) (s := fderiv ℝ d x v)
    (U := realHessian a x v v) (V := realHessian b x v v)
    (R := (b x*fderiv ℝ a x v-a x*fderiv ℝ b x v)/(a x+b x))
  rw [hermitianQuotientRatioFieldTwo_realHessian_normalized ha hb hc hd hA hB hC hD
    hc0 hd0 hA1 hB1 hC0 hD0 ht.ne' v]
  convert hbound using 1 <;> field_simp [ht.ne'] <;> ring

end PowerConvexity
