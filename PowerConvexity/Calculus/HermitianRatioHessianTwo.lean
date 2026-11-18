import PowerConvexity.Calculus.RealHessianQuotient

/-! # The actual real Hessian of the Hermitian trace-determinant ratio at a diagonal point -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped ContDiff
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def hermitianRatioFieldTwo (a b c d : E → ℝ) (x : E) : ℝ :=
  traceDetRatioTwo (a x+b x) (a x*b x-(c x)^2-(d x)^2)

theorem hermitianRatioFieldTwo_realHessian_diagonal
    {a b c d : E → ℝ} {x : E}
    (ha : ContDiffAt ℝ 2 a x) (hb : ContDiffAt ℝ 2 b x)
    (hc : ContDiffAt ℝ 2 c x) (hd : ContDiffAt ℝ 2 d x)
    (hc0 : c x = 0) (hd0 : d x = 0) (ht : a x+b x ≠ 0) (v : E) :
    realHessian (hermitianRatioFieldTwo a b c d) x v v =
      (1+(b x)^2/(a x+b x)^2)*realHessian a x v v+
      (1+(a x)^2/(a x+b x)^2)*realHessian b x v v-
      2*((b x*fderiv ℝ a x v-a x*fderiv ℝ b x v)^2+
        (a x+b x)^2*((fderiv ℝ c x v)^2+(fderiv ℝ d x v)^2))/(a x+b x)^3 := by
  let T : E → ℝ := fun y => a y+b y
  let N : E → ℝ := fun y => a y*b y-c y*c y-d y*d y
  have hT : ContDiffAt ℝ 2 T x := ha.add hb
  have hN : ContDiffAt ℝ 2 N x := ((ha.mul hb).sub (hc.mul hc)).sub (hd.mul hd)
  have hTx : T x = a x+b x := rfl
  have hNx : N x = a x*b x := by simp [N,hc0,hd0]
  have hDT : fderiv ℝ T x v = fderiv ℝ a x v+fderiv ℝ b x v := by
    rw [show T = fun y => a y+b y from rfl,
      fderiv_fun_add (ha.differentiableAt (by norm_num)) (hb.differentiableAt (by norm_num)),add_apply]
  have hDN : fderiv ℝ N x v = b x*fderiv ℝ a x v+a x*fderiv ℝ b x v := by
    unfold N
    rw [fderiv_fun_sub (((ha.mul hb).sub (hc.mul hc)).differentiableAt (by norm_num))
      ((hd.mul hd).differentiableAt (by norm_num)),
      fderiv_fun_sub ((ha.mul hb).differentiableAt (by norm_num)) ((hc.mul hc).differentiableAt (by norm_num)),
      fderiv_fun_mul (ha.differentiableAt (by norm_num)) (hb.differentiableAt (by norm_num)),
      fderiv_fun_mul (hc.differentiableAt (by norm_num)) (hc.differentiableAt (by norm_num)),
      fderiv_fun_mul (hd.differentiableAt (by norm_num)) (hd.differentiableAt (by norm_num))]
    simp only [sub_apply,add_apply,smul_apply,smul_eq_mul,hc0,hd0,zero_mul,add_zero,sub_zero]
    ring
  have hHT : realHessian T x v v = realHessian a x v v+realHessian b x v v := by
    rw [show T = fun y => a y+b y from rfl,realHessian_add ha hb,add_apply,add_apply]
  have hHN : realHessian N x v v =
      b x*realHessian a x v v+a x*realHessian b x v v+
        2*(fderiv ℝ a x v*fderiv ℝ b x v-(fderiv ℝ c x v)^2-(fderiv ℝ d x v)^2) := by
    unfold N
    rw [realHessian_sub_at ((ha.mul hb).sub (hc.mul hc)) (hd.mul hd),sub_apply,sub_apply,
      realHessian_sub_at (ha.mul hb) (hc.mul hc),sub_apply,sub_apply,
      realHessian_mul_real_at ha hb,realHessian_mul_real_at hc hc,realHessian_mul_real_at hd hd]
    rw [hc0,hd0]
    ring
  have he : hermitianRatioFieldTwo a b c d = fun y => traceDetRatioTwo (T y) (N y) := by
    funext y
    simp only [hermitianRatioFieldTwo,T,N,pow_two]
  rw [he,realHessian_traceDetRatioTwo hT hN ht,hTx,hNx,hDT,hDN,hHT,hHN]
  field_simp [ht]
  <;> ring

end PowerConvexity
