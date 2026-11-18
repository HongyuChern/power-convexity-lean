import PowerConvexity.Analysis.SmoothPositivePrimitive
import PowerConvexity.Calculus.RealHessianScalarComposition
import CHS.Calculus.PotentialConstants
import CHS.Calculus.QuadraticPerturbation

/-! # An exact smooth maximum and its actual Hessian formula -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Filter
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def exactSmoothMaximum (eps : ℝ) (f g : E → ℝ) : E → ℝ :=
  fun x => g x+eps*smoothPositivePrimitive
    (eps⁻¹*(f x-g x)+(1-smoothPositivePrimitive 1))

theorem exactSmoothMaximum_eq_left {eps : ℝ} (heps : 0 < eps)
    (f g : E → ℝ) {x : E} (hx : eps ≤ f x-g x) :
    exactSmoothMaximum eps f g x = f x := by
  have h1 : 1 ≤ eps⁻¹*(f x-g x) := by
    simpa only [inv_mul_cancel₀ heps.ne'] using
      mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr heps.le)
  have hs : 1 ≤ eps⁻¹*(f x-g x)+(1-smoothPositivePrimitive 1) := by
    linarith [smoothPositivePrimitive_one_mem_Icc.2]
  unfold exactSmoothMaximum
  rw [smoothPositivePrimitive_affine_of_one_le hs]
  field_simp
  <;> ring

theorem exactSmoothMaximum_eq_right {eps : ℝ} (heps : 0 < eps)
    (f g : E → ℝ) {x : E} (hx : f x-g x ≤ -eps) :
    exactSmoothMaximum eps f g x = g x := by
  have h1 : eps⁻¹*(f x-g x) ≤ -1 := by
    simpa only [mul_neg,inv_mul_cancel₀ heps.ne'] using
      mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr heps.le)
  have hs : eps⁻¹*(f x-g x)+(1-smoothPositivePrimitive 1) ≤ 0 := by
    linarith [smoothPositivePrimitive_one_mem_Icc.1]
  simp only [exactSmoothMaximum,smoothPositivePrimitive_zero_of_nonpos hs,mul_zero,add_zero]

theorem exactSmoothMaximum_contDiffAt {f g : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 4 f x) (hg : ContDiffAt ℝ 4 g x) (eps : ℝ) :
    ContDiffAt ℝ 4 (exactSmoothMaximum eps f g) x := by
  have hp : ContDiff ℝ 4 smoothPositivePrimitive :=
    (contDiff_infty.mp smoothPositivePrimitive_contDiff) 4
  exact hg.add (contDiffAt_const.mul (hp.contDiffAt.comp x
    ((contDiffAt_const.mul (hf.sub hg)).add contDiffAt_const)))

theorem realHessian_exactSmoothMaximum {eps : ℝ} (heps : 0 < eps)
    {f g : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x)
    (v w : E) :
    let s := eps⁻¹*(f x-g x)+(1-smoothPositivePrimitive 1)
    realHessian (exactSmoothMaximum eps f g) x v w =
      Real.smoothTransition s*realHessian f x v w+
      (1-Real.smoothTransition s)*realHessian g x v w+
      (eps⁻¹*deriv Real.smoothTransition s)*
        (fderiv ℝ f x v-fderiv ℝ g x v)*(fderiv ℝ f x w-fderiv ℝ g x w) := by
  let S : E → ℝ := fun y => eps⁻¹*(f y-g y)+(1-smoothPositivePrimitive 1)
  have hS : ContDiffAt ℝ 2 S x :=
    (contDiffAt_const.mul (hf.sub hg)).add contDiffAt_const
  have hp : ContDiff ℝ 2 smoothPositivePrimitive :=
    (contDiff_infty.mp smoothPositivePrimitive_contDiff) 2
  have hpS : ContDiffAt ℝ 2 (fun y => smoothPositivePrimitive (S y)) x :=
    hp.contDiffAt.comp x hS
  have hSH (a b : E) : realHessian S x a b =
      eps⁻¹*(realHessian f x a b-realHessian g x a b) := by
    change realHessian (fun y => eps⁻¹*(f y-g y)+(1-smoothPositivePrimitive 1)) x a b = _
    rw [realHessian_add_const,realHessian_const_mul_at (hf.sub hg),realHessian_sub_at hf hg]
    simp
  have hSD (a : E) : fderiv ℝ S x a = eps⁻¹*(fderiv ℝ f x a-fderiv ℝ g x a) := by
    change fderiv ℝ (fun y => eps⁻¹*(f y-g y)+(1-smoothPositivePrimitive 1)) x a = _
    rw [fderiv_add_const,fderiv_const_mul
      ((hf.differentiableAt (by norm_num)).fun_sub (hg.differentiableAt (by norm_num))),
      fderiv_fun_sub (hf.differentiableAt (by norm_num)) (hg.differentiableAt (by norm_num))]
    simp
  change realHessian (fun y => g y+eps*smoothPositivePrimitive (S y)) x v w = _
  rw [realHessian_add hg (contDiffAt_const.mul hpS),add_apply,add_apply,
    realHessian_const_mul_at hpS,smul_apply,smul_apply,smul_eq_mul,
    realHessian_scalar_composition hp hS,
    smoothPositivePrimitive_deriv,hSH,hSD,hSD]
  change realHessian g x v w+eps*(Real.smoothTransition (S x)*
    (eps⁻¹*(realHessian f x v w-realHessian g x v w))+
    deriv Real.smoothTransition (S x)*(eps⁻¹*(fderiv ℝ f x v-fderiv ℝ g x v))*
      (eps⁻¹*(fderiv ℝ f x w-fderiv ℝ g x w))) = _
  dsimp only [S]
  field_simp
  <;> ring

end PowerConvexity
