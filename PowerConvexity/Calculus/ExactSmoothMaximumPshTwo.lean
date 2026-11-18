import PowerConvexity.Calculus.ExactSmoothMaximum
import PowerConvexity.Calculus.PairedLeviMatrixTwo
import PowerConvexity.Calculus.ComplexLeviPairPositiveTwo

/-! # The exact smooth maximum preserves actual strict plurisubharmonicity -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]

theorem exactSmoothMaximum_strictPsh_two
    (e : Module.Basis (Fin 2) ℂ E) {eps : ℝ} (heps : 0 < eps)
    {f g : E → ℝ} {x : E} (hf : ContDiffAt ℝ 4 f x) (hg : ContDiffAt ℝ 4 g x)
    (hpf : (complexHessian e (fun j => Complex.I • e j) f x).PosDef)
    (hpg : (complexHessian e (fun j => Complex.I • e j) g x).PosDef) :
    (complexHessian e (fun j => Complex.I • e j) (exactSmoothMaximum eps f g) x).PosDef := by
  have hf2 : ContDiffAt ℝ 2 f x := hf.of_le (by norm_num)
  have hg2 : ContDiffAt ℝ 2 g x := hg.of_le (by norm_num)
  apply complexHessian_posDef_of_paired_positive_two e
    ((exactSmoothMaximum_contDiffAt hf hg eps).of_le (by norm_num))
  intro v hv
  let s := eps⁻¹*(f x-g x)+(1-smoothPositivePrimitive 1)
  let a := Real.smoothTransition s
  let b := eps⁻¹*deriv Real.smoothTransition s
  have ha0 : 0 ≤ a := Real.smoothTransition.nonneg s
  have ha1 : a ≤ 1 := Real.smoothTransition.le_one s
  have hb0 : 0 ≤ b := mul_nonneg (inv_nonneg.mpr heps.le)
    Real.smoothTransition.monotone.deriv_nonneg
  have hfpos := complexHessian_posDef_paired_positive_two e hf2 hpf v hv
  have hgpos := complexHessian_posDef_paired_positive_two e hg2 hpg v hv
  have hlin : 0 < a*(realHessian f x v v+realHessian f x (Complex.I • v) (Complex.I • v))+
      (1-a)*(realHessian g x v v+realHessian g x (Complex.I • v) (Complex.I • v)) := by
    by_cases ha : a = 0
    · simpa only [ha,zero_mul,sub_zero,one_mul,zero_add] using hgpos
    · exact add_pos_of_pos_of_nonneg (mul_pos (lt_of_le_of_ne ha0 (Ne.symm ha)) hfpos)
        (mul_nonneg (sub_nonneg.mpr ha1) hgpos.le)
  have hs0 := mul_nonneg hb0 (sq_nonneg (fderiv ℝ f x v-fderiv ℝ g x v))
  have hs1 := mul_nonneg hb0
    (sq_nonneg (fderiv ℝ f x (Complex.I • v)-fderiv ℝ g x (Complex.I • v)))
  rw [realHessian_exactSmoothMaximum heps hf2 hg2,realHessian_exactSmoothMaximum heps hf2 hg2]
  change 0 < a*realHessian f x v v+(1-a)*realHessian g x v v+
    b*(fderiv ℝ f x v-fderiv ℝ g x v)*(fderiv ℝ f x v-fderiv ℝ g x v)+
    (a*realHessian f x (Complex.I • v) (Complex.I • v)+
    (1-a)*realHessian g x (Complex.I • v) (Complex.I • v)+
    b*(fderiv ℝ f x (Complex.I • v)-fderiv ℝ g x (Complex.I • v))*
      (fderiv ℝ f x (Complex.I • v)-fderiv ℝ g x (Complex.I • v)))
  nlinarith

end PowerConvexity
