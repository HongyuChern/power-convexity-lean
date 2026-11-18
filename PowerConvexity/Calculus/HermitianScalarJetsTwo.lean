import PowerConvexity.Calculus.RealHessianQuotient

/-! # Actual determinant and adjugate-trace jets in real Hermitian coordinates -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped ContDiff
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def hermitianDetFieldTwo (a b c d : E → ℝ) (x : E) : ℝ :=
  a x*b x-c x*c x-d x*d x
noncomputable def hermitianAdjTraceFieldTwo (a b c d A B C D : E → ℝ) (x : E) : ℝ :=
  a x*B x+b x*A x-2*(c x*C x+d x*D x)

theorem hermitianDetFieldTwo_contDiffAt {a b c d : E → ℝ} {x : E}
    (ha : ContDiffAt ℝ 2 a x) (hb : ContDiffAt ℝ 2 b x)
    (hc : ContDiffAt ℝ 2 c x) (hd : ContDiffAt ℝ 2 d x) :
    ContDiffAt ℝ 2 (hermitianDetFieldTwo a b c d) x :=
  ((ha.mul hb).sub (hc.mul hc)).sub (hd.mul hd)

theorem hermitianAdjTraceFieldTwo_contDiffAt {a b c d A B C D : E → ℝ} {x : E}
    (ha : ContDiffAt ℝ 2 a x) (hb : ContDiffAt ℝ 2 b x)
    (hc : ContDiffAt ℝ 2 c x) (hd : ContDiffAt ℝ 2 d x)
    (hA : ContDiffAt ℝ 2 A x) (hB : ContDiffAt ℝ 2 B x)
    (hC : ContDiffAt ℝ 2 C x) (hD : ContDiffAt ℝ 2 D x) :
    ContDiffAt ℝ 2 (hermitianAdjTraceFieldTwo a b c d A B C D) x :=
  ((ha.mul hB).add (hb.mul hA)).sub (contDiffAt_const.mul ((hc.mul hC).add (hd.mul hD)))

theorem hermitianDetFieldTwo_fderiv_diagonal {a b c d : E → ℝ} {x : E}
    (ha : ContDiffAt ℝ 2 a x) (hb : ContDiffAt ℝ 2 b x)
    (hc : ContDiffAt ℝ 2 c x) (hd : ContDiffAt ℝ 2 d x)
    (hc0 : c x = 0) (hd0 : d x = 0) (v : E) :
    fderiv ℝ (hermitianDetFieldTwo a b c d) x v =
      b x*fderiv ℝ a x v+a x*fderiv ℝ b x v := by
  unfold hermitianDetFieldTwo
  rw [fderiv_fun_sub (((ha.mul hb).sub (hc.mul hc)).differentiableAt (by norm_num))
    ((hd.mul hd).differentiableAt (by norm_num)),
    fderiv_fun_sub ((ha.mul hb).differentiableAt (by norm_num)) ((hc.mul hc).differentiableAt (by norm_num)),
    fderiv_fun_mul (ha.differentiableAt (by norm_num)) (hb.differentiableAt (by norm_num)),
    fderiv_fun_mul (hc.differentiableAt (by norm_num)) (hc.differentiableAt (by norm_num)),
    fderiv_fun_mul (hd.differentiableAt (by norm_num)) (hd.differentiableAt (by norm_num))]
  simp only [sub_apply,add_apply,smul_apply,smul_eq_mul,hc0,hd0,zero_mul,add_zero,sub_zero]
  ring

theorem hermitianDetFieldTwo_realHessian_diagonal {a b c d : E → ℝ} {x : E}
    (ha : ContDiffAt ℝ 2 a x) (hb : ContDiffAt ℝ 2 b x)
    (hc : ContDiffAt ℝ 2 c x) (hd : ContDiffAt ℝ 2 d x)
    (hc0 : c x = 0) (hd0 : d x = 0) (v : E) :
    realHessian (hermitianDetFieldTwo a b c d) x v v =
      b x*realHessian a x v v+a x*realHessian b x v v+
        2*(fderiv ℝ a x v*fderiv ℝ b x v-(fderiv ℝ c x v)^2-(fderiv ℝ d x v)^2) := by
  unfold hermitianDetFieldTwo
  rw [realHessian_sub_at ((ha.mul hb).sub (hc.mul hc)) (hd.mul hd),sub_apply,sub_apply,
    realHessian_sub_at (ha.mul hb) (hc.mul hc),sub_apply,sub_apply,
    realHessian_mul_real_at ha hb,realHessian_mul_real_at hc hc,realHessian_mul_real_at hd hd]
  rw [hc0,hd0]
  ring

theorem hermitianAdjTraceFieldTwo_fderiv_normalized {a b c d A B C D : E → ℝ} {x : E}
    (ha : ContDiffAt ℝ 2 a x) (hb : ContDiffAt ℝ 2 b x)
    (hc : ContDiffAt ℝ 2 c x) (hd : ContDiffAt ℝ 2 d x)
    (hA : ContDiffAt ℝ 2 A x) (hB : ContDiffAt ℝ 2 B x)
    (hC : ContDiffAt ℝ 2 C x) (hD : ContDiffAt ℝ 2 D x)
    (hc0 : c x = 0) (hd0 : d x = 0) (hA1 : A x = 1) (hB1 : B x = 1)
    (hC0 : C x = 0) (hD0 : D x = 0) (v : E) :
    fderiv ℝ (hermitianAdjTraceFieldTwo a b c d A B C D) x v =
      fderiv ℝ a x v+fderiv ℝ b x v+a x*fderiv ℝ B x v+b x*fderiv ℝ A x v := by
  unfold hermitianAdjTraceFieldTwo
  rw [fderiv_fun_sub (((ha.mul hB).add (hb.mul hA)).differentiableAt (by norm_num))
    ((contDiffAt_const.mul ((hc.mul hC).add (hd.mul hD))).differentiableAt (by norm_num)),
    fderiv_fun_add ((ha.mul hB).differentiableAt (by norm_num)) ((hb.mul hA).differentiableAt (by norm_num)),
    fderiv_const_mul (((hc.mul hC).add (hd.mul hD)).differentiableAt (by norm_num)) (2:ℝ),
    fderiv_fun_add ((hc.mul hC).differentiableAt (by norm_num)) ((hd.mul hD).differentiableAt (by norm_num)),
    fderiv_fun_mul (ha.differentiableAt (by norm_num)) (hB.differentiableAt (by norm_num)),
    fderiv_fun_mul (hb.differentiableAt (by norm_num)) (hA.differentiableAt (by norm_num)),
    fderiv_fun_mul (hc.differentiableAt (by norm_num)) (hC.differentiableAt (by norm_num)),
    fderiv_fun_mul (hd.differentiableAt (by norm_num)) (hD.differentiableAt (by norm_num))]
  simp only [sub_apply,add_apply,smul_apply,smul_eq_mul,hc0,hd0,hA1,hB1,hC0,hD0,
    zero_mul,one_mul,mul_zero,add_zero,sub_zero]
  ring

theorem hermitianAdjTraceFieldTwo_realHessian_normalized {a b c d A B C D : E → ℝ} {x : E}
    (ha : ContDiffAt ℝ 2 a x) (hb : ContDiffAt ℝ 2 b x)
    (hc : ContDiffAt ℝ 2 c x) (hd : ContDiffAt ℝ 2 d x)
    (hA : ContDiffAt ℝ 2 A x) (hB : ContDiffAt ℝ 2 B x)
    (hC : ContDiffAt ℝ 2 C x) (hD : ContDiffAt ℝ 2 D x)
    (hc0 : c x = 0) (hd0 : d x = 0) (hA1 : A x = 1) (hB1 : B x = 1)
    (hC0 : C x = 0) (hD0 : D x = 0) (v : E) :
    realHessian (hermitianAdjTraceFieldTwo a b c d A B C D) x v v =
      realHessian a x v v+realHessian b x v v+a x*realHessian B x v v+b x*realHessian A x v v+
      2*(fderiv ℝ a x v*fderiv ℝ B x v+fderiv ℝ b x v*fderiv ℝ A x v)-
      4*(fderiv ℝ c x v*fderiv ℝ C x v+fderiv ℝ d x v*fderiv ℝ D x v) := by
  unfold hermitianAdjTraceFieldTwo
  rw [realHessian_sub_at ((ha.mul hB).add (hb.mul hA))
    (contDiffAt_const.mul ((hc.mul hC).add (hd.mul hD))),sub_apply,sub_apply,
    realHessian_add (ha.mul hB) (hb.mul hA),add_apply,add_apply,
    realHessian_const_mul_at ((hc.mul hC).add (hd.mul hD)) 2,smul_apply,smul_apply,
    realHessian_add (hc.mul hC) (hd.mul hD),add_apply,add_apply,
    realHessian_mul_real_at ha hB,realHessian_mul_real_at hb hA,
    realHessian_mul_real_at hc hC,realHessian_mul_real_at hd hD]
  rw [hc0,hd0,hA1,hB1,hC0,hD0]
  simp only [smul_eq_mul]
  ring

end PowerConvexity
