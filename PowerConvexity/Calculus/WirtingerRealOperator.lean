import PowerConvexity.Analysis.GradientStrongMinimum
import PowerConvexity.Calculus.AppendixCLocalEstimate

/-! # Real contraction and gradient bounds for the scalar Wirtinger operator -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff Topology

namespace PowerConvexity
open CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_dz_ofReal_le {f : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (a b : E) :
    ‖dz a b (fun y => (f y : ℂ)) x‖ ≤
      ((‖a‖ + ‖b‖) / 2) * ‖fderiv ℝ f x‖ := by
  have hz := complexGradient_real_entry hf (fun _ : Fin 1 => a) (fun _ : Fin 1 => b) 0
  change dz a b (fun y => (f y : ℂ)) x = _ at hz
  rw [hz, norm_mul, norm_inv]
  have htriangle := norm_sub_le (fderiv ℝ f x a : ℂ) (Complex.I * (fderiv ℝ f x b : ℂ))
  simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs] at htriangle
  have ha := (fderiv ℝ f x).le_opNorm a
  have hb := (fderiv ℝ f x).le_opNorm b
  rw [Real.norm_eq_abs] at ha hb
  norm_num
  nlinarith

theorem mixed_dz_real_eq {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (a b : E) :
    (dz a (-b) (dz a b (fun y => (f y : ℂ))) x).re =
      (realHessian f x a a + realHessian f x b b) / 4 := by
  have hfc : ContDiffAt ℝ 2 (fun y => (f y : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hf
  rw [dz_comm_at hfc a (-b) a b]
  have h := complexHessian_real_entry hf (fun _ : Fin 1 => a) (fun _ : Fin 1 => b) 0 0
  change dz a b (dz a (-b) (fun y => (f y : ℂ))) x = _ at h
  rw [h]
  simp only [Complex.mul_re, Complex.add_re, Complex.sub_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im]
  norm_num
  ring

noncomputable def scalarHessianContraction : (ℂ →L[ℝ] ℂ →L[ℝ] ℝ) →ₗ[ℝ] ℝ where
  toFun H := (H 1 1 + H Complex.I Complex.I) / 4
  map_add' H K := by simp only [add_apply]; ring
  map_smul' c H := by simp only [smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem scalarHessianContraction_positive : HessianPositive scalarHessianContraction := by
  intro H hH
  change 0 ≤ (H 1 1 + H Complex.I Complex.I) / 4
  exact div_nonneg (add_nonneg (hH 1) (hH Complex.I)) (by norm_num)

theorem scalarHessianContraction_rankOne (v : ℂ) :
    scalarHessianContraction (realRankOneForm v) = (1/4 : ℝ) * ‖v‖^2 := by
  simp only [scalarHessianContraction, LinearMap.coe_mk, AddHom.coe_mk,
    realRankOneForm, ContinuousLinearMap.smulRight_apply, smul_apply, smul_eq_mul,
    innerSL_apply_apply, Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im]
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

theorem scalarHessianContraction_trace :
    scalarHessianContraction (realInnerForm (E := ℂ)) = (1/2 : ℝ) := by
  change (inner ℝ (1 : ℂ) 1 + inner ℝ Complex.I Complex.I) / 4 = 1/2
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  norm_num

end PowerConvexity
