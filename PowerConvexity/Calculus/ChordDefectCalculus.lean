import PowerConvexity.Calculus.RealHessianRules
import CHS.Calculus.AffinePullback

/-! # Actual first and second derivatives of a two-point chord defect -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def chordLinearMap (a b : ℝ) : E × E →L[ℝ] E :=
  a • ContinuousLinearMap.fst ℝ E E+b • ContinuousLinearMap.snd ℝ E E

noncomputable def chordDefect (a b : ℝ) (f : E → ℝ) (z : E × E) : ℝ :=
  f (a • z.1+b • z.2)-a*f z.1-b*f z.2

theorem chordDefect_contDiffAt {f : E → ℝ} {x y : E} (a b : ℝ)
    (hx : ContDiffAt ℝ 2 f x) (hy : ContDiffAt ℝ 2 f y)
    (hz : ContDiffAt ℝ 2 f (a • x+b • y)) :
    ContDiffAt ℝ 2 (chordDefect a b f) (x,y) := by
  have hC := hz.comp (x,y) (chordLinearMap (E := E) a b).contDiff.contDiffAt
  have hX := hx.comp (x,y) (ContinuousLinearMap.fst ℝ E E).contDiff.contDiffAt
  have hY := hy.comp (x,y) (ContinuousLinearMap.snd ℝ E E).contDiff.contDiffAt
  exact (hC.sub (contDiffAt_const.mul hX)).sub (contDiffAt_const.mul hY)

theorem chordDefect_fderiv {f : E → ℝ} {x y : E} (a b : ℝ)
    (hx : DifferentiableAt ℝ f x) (hy : DifferentiableAt ℝ f y)
    (hz : DifferentiableAt ℝ f (a • x+b • y)) :
    fderiv ℝ (chordDefect a b f) (x,y) =
      (fderiv ℝ f (a • x+b • y)).comp (chordLinearMap a b)-
        a • (fderiv ℝ f x).comp (ContinuousLinearMap.fst ℝ E E)-
        b • (fderiv ℝ f y).comp (ContinuousLinearMap.snd ℝ E E) := by
  have hC := hz.hasFDerivAt.comp (x,y) (chordLinearMap (E := E) a b).hasFDerivAt
  have hX := hx.hasFDerivAt.comp (x,y) (ContinuousLinearMap.fst ℝ E E).hasFDerivAt
  have hY := hy.hasFDerivAt.comp (x,y) (ContinuousLinearMap.snd ℝ E E).hasFDerivAt
  exact ((hC.sub (hX.const_smul a)).sub (hY.const_smul b)).fderiv

theorem realHessian_comp_linear {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : F → ℝ} (T : E →L[ℝ] F) {x : E} (hf : ContDiffAt ℝ 2 f (T x)) (v w : E) :
    realHessian (fun y => f (T y)) x v w = realHessian f (T x) (T v) (T w) := by
  simpa only [zero_add] using realHessian_comp_affine T 0 (by simpa only [zero_add] using hf) v w

theorem chordDefect_realHessian {f : E → ℝ} {x y : E} (a b : ℝ)
    (hx : ContDiffAt ℝ 2 f x) (hy : ContDiffAt ℝ 2 f y)
    (hz : ContDiffAt ℝ 2 f (a • x+b • y)) (v w : E × E) :
    realHessian (chordDefect a b f) (x,y) v w =
      realHessian f (a • x+b • y) (a • v.1+b • v.2) (a • w.1+b • w.2)-
      a*realHessian f x v.1 w.1-b*realHessian f y v.2 w.2 := by
  have hC := hz.comp (x,y) (chordLinearMap (E := E) a b).contDiff.contDiffAt
  have hX := hx.comp (x,y) (ContinuousLinearMap.fst ℝ E E).contDiff.contDiffAt
  have hY := hy.comp (x,y) (ContinuousLinearMap.snd ℝ E E).contDiff.contDiffAt
  change realHessian (fun z : E × E => f (chordLinearMap a b z)-
    a*f z.1-b*f z.2) (x,y) v w = _
  change ContDiffAt ℝ 2 (fun z : E × E => f (chordLinearMap a b z)) (x,y) at hC
  change ContDiffAt ℝ 2 (fun z : E × E => f z.1) (x,y) at hX
  change ContDiffAt ℝ 2 (fun z : E × E => f z.2) (x,y) at hY
  have hAX : ContDiffAt ℝ 2 (fun z : E × E => a*f z.1) (x,y) := contDiffAt_const.mul hX
  have hBY : ContDiffAt ℝ 2 (fun z : E × E => b*f z.2) (x,y) := contDiffAt_const.mul hY
  rw [realHessian_sub_at (hC.sub hAX) hBY,
    realHessian_sub_at hC hAX,realHessian_const_mul_at hX a,
    realHessian_const_mul_at hY b]
  simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
  rw [realHessian_comp_linear (f := f) (x := (x,y)) (chordLinearMap a b) hz v w]
  have hfst := realHessian_comp_linear (f := f) (x := (x,y)) (ContinuousLinearMap.fst ℝ E E) hx v w
  have hsnd := realHessian_comp_linear (f := f) (x := (x,y)) (ContinuousLinearMap.snd ℝ E E) hy v w
  simp only [ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd'] at hfst hsnd
  rw [hfst,hsnd]
  rfl

theorem chordDefect_localMax_gradients {f : E → ℝ} {x y : E} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hx : DifferentiableAt ℝ f x) (hy : DifferentiableAt ℝ f y)
    (hz : DifferentiableAt ℝ f (a • x+b • y))
    (hm : IsLocalMax (chordDefect a b f) (x,y)) :
    fderiv ℝ f x = fderiv ℝ f (a • x+b • y) ∧
      fderiv ℝ f y = fderiv ℝ f (a • x+b • y) := by
  have hD := hm.fderiv_eq_zero
  rw [chordDefect_fderiv a b hx hy hz] at hD
  constructor
  · ext v
    have h := congrArg (fun L : E × E →L[ℝ] ℝ => L (v,0)) hD
    simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply,chordLinearMap,ContinuousLinearMap.add_apply,
      ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',
      map_zero,smul_zero,add_zero,map_smul,smul_eq_mul,sub_zero,zero_mul,ContinuousLinearMap.zero_apply] at h
    have hp : a*(fderiv ℝ f (a • x+b • y) v-fderiv ℝ f x v) = 0 := by linarith
    exact (sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left ha.ne')).symm
  · ext v
    have h := congrArg (fun L : E × E →L[ℝ] ℝ => L (0,v)) hD
    simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply,chordLinearMap,ContinuousLinearMap.add_apply,
      ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',
      map_zero,smul_zero,zero_add,map_smul,smul_eq_mul,sub_zero,zero_mul,ContinuousLinearMap.zero_apply] at h
    have hp : b*(fderiv ℝ f (a • x+b • y) v-fderiv ℝ f y v) = 0 := by linarith
    exact (sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left hb.ne')).symm

theorem chordDefect_localMax_weighted_Hessian {f : E → ℝ} {x y : E} (a b A B : ℝ)
    (hx : ContDiffAt ℝ 2 f x) (hy : ContDiffAt ℝ 2 f y)
    (hz : ContDiffAt ℝ 2 f (a • x+b • y))
    (hm : IsLocalMax (chordDefect a b f) (x,y)) (v : E) :
    (a*A+b*B)^2*realHessian f (a • x+b • y) v v-
      a*A^2*realHessian f x v v-b*B^2*realHessian f y v v ≤ 0 := by
  have h := realHessian_nonpos_of_isLocalMax (chordDefect_contDiffAt a b hx hy hz) hm (A • v,B • v)
  rw [chordDefect_realHessian a b hx hy hz] at h
  have he : a • (A • v)+b • (B • v) = (a*A+b*B) • v := by
    rw [smul_smul,smul_smul,add_smul]
  simp only [he,map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul] at h
  convert h using 1 <;> ring

end PowerConvexity
