import PowerConvexity.Calculus.QuotientRatioHessianDirectionBoundTwo
import PowerConvexity.Analysis.DualSquareContraction

/-! # Homogeneous actual Hessian inequality with operator norms -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open scoped ContDiff
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem continuousLinearMap_apply_abs_le_of_unit {D : E →L[ℝ] ℝ} {v : E}
    (hv : ‖v‖ = 1) : |D v| ≤ ‖D‖ := by
  simpa only [Real.norm_eq_abs,hv,mul_one] using D.le_opNorm v

theorem continuousBilinearMap_apply_abs_le_of_unit {H : E →L[ℝ] E →L[ℝ] ℝ} {v : E}
    (hv : ‖v‖ = 1) : |H v v| ≤ ‖H‖ := by
  calc
    _ ≤ ‖H v‖*‖v‖ := (H v).le_opNorm v
    _ ≤ (‖H‖*‖v‖)*‖v‖ := mul_le_mul_of_nonneg_right (H.le_opNorm v) (norm_nonneg v)
    _ = _ := by rw [hv]; ring

theorem hermitianQuotientRatioFieldTwo_quadratic_bound
    {a b c d A B C D : E → ℝ} {x : E}
    (ha : ContDiffAt ℝ 2 a x) (hb : ContDiffAt ℝ 2 b x)
    (hc : ContDiffAt ℝ 2 c x) (hd : ContDiffAt ℝ 2 d x)
    (hA : ContDiffAt ℝ 2 A x) (hB : ContDiffAt ℝ 2 B x)
    (hC : ContDiffAt ℝ 2 C x) (hD : ContDiffAt ℝ 2 D x)
    (hc0 : c x = 0) (hd0 : d x = 0) (hA1 : A x = 1) (hB1 : B x = 1)
    (hC0 : C x = 0) (hD0 : D x = 0)
    (ha0 : 0 ≤ a x) (hb0 : 0 ≤ b x) (ht : 0 < a x+b x)
    {K : ℝ} (hK : 0 ≤ K)
    (hDA : ‖fderiv ℝ A x‖ ≤ K) (hDB : ‖fderiv ℝ B x‖ ≤ K)
    (hDC : ‖fderiv ℝ C x‖ ≤ K) (hDD : ‖fderiv ℝ D x‖ ≤ K)
    (hHA : ‖realHessian A x‖ ≤ K) (hHB : ‖realHessian B x‖ ≤ K) :
    let R : E →L[ℝ] ℝ := (a x+b x)⁻¹ • (b x • fderiv ℝ a x-a x • fderiv ℝ b x)
    let S := ‖fderiv ℝ a x‖+‖fderiv ℝ b x‖+‖fderiv ℝ c x‖+‖fderiv ℝ d x‖
    ∀ v : E,
      realHessian (hermitianQuotientRatioFieldTwo a b c d A B C D) x v v ≤
        (1+(b x)^2/(a x+b x)^2)*realHessian a x v v+
        (1+(a x)^2/(a x+b x)^2)*realHessian b x v v+
        ((2*K+22*K^2)*(a x+b x)+8*K*S)*‖v‖^2-
        1/(a x+b x)*((R v)^2+(fderiv ℝ c x v)^2+(fderiv ℝ d x v)^2) := by
  dsimp only
  let R : E →L[ℝ] ℝ := (a x+b x)⁻¹ • (b x • fderiv ℝ a x-a x • fderiv ℝ b x)
  let S := ‖fderiv ℝ a x‖+‖fderiv ℝ b x‖+‖fderiv ℝ c x‖+‖fderiv ℝ d x‖
  let H0 := (1+(b x)^2/(a x+b x)^2) • realHessian a x+
    (1+(a x)^2/(a x+b x)^2) • realHessian b x
  let K0 := (2*K+22*K^2)*(a x+b x)+8*K*S
  let Hup := H0+K0 • realInnerForm (E := E)-
    (1/(a x+b x)) • (dualSquareForm R+dualSquareForm (fderiv ℝ c x)+dualSquareForm (fderiv ℝ d x))
  have hRv (v : E) : R v = (b x*fderiv ℝ a x v-a x*fderiv ℝ b x v)/(a x+b x) := by
    simp only [R,smul_apply,sub_apply,smul_eq_mul,div_eq_mul_inv]
    ring
  have hinner (v : E) : realInnerForm (E := E) v v = ‖v‖^2 := by
    change inner ℝ v v = _
    exact real_inner_self_eq_norm_sq v
  have hup := bilinear_order_of_unit_sphere
    (realHessian (hermitianQuotientRatioFieldTwo a b c d A B C D) x) Hup (by
    intro v hv
    have hD1 := continuousLinearMap_apply_abs_le_of_unit (D := fderiv ℝ a x) hv
    have hD2 := continuousLinearMap_apply_abs_le_of_unit (D := fderiv ℝ b x) hv
    have hD3 := continuousLinearMap_apply_abs_le_of_unit (D := fderiv ℝ c x) hv
    have hD4 := continuousLinearMap_apply_abs_le_of_unit (D := fderiv ℝ d x) hv
    have hsum := mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add (add_le_add hD1 hD2) hD3) hD4) (show 0 ≤ 8*K by positivity)
    have hh := hermitianQuotientRatioFieldTwo_direction_bound ha hb hc hd hA hB hC hD
      hc0 hd0 hA1 hB1 hC0 hD0 ha0 hb0 ht v hK
      ((continuousLinearMap_apply_abs_le_of_unit hv).trans hDA)
      ((continuousLinearMap_apply_abs_le_of_unit hv).trans hDB)
      ((continuousLinearMap_apply_abs_le_of_unit hv).trans hDC)
      ((continuousLinearMap_apply_abs_le_of_unit hv).trans hDD)
      ((continuousBilinearMap_apply_abs_le_of_unit hv).trans hHA)
      ((continuousBilinearMap_apply_abs_le_of_unit hv).trans hHB)
    simp only [Hup,H0,K0,S,sub_apply,add_apply,smul_apply,smul_eq_mul,
      hinner,hv,one_pow,mul_one,
      dualSquareForm_apply,hRv]
    linarith)
  intro v
  simpa only [Hup,H0,K0,S,R,sub_apply,add_apply,smul_apply,smul_eq_mul,
    hinner,dualSquareForm_apply,pow_two] using hup v

end PowerConvexity
