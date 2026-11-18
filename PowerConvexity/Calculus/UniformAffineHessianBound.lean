import PowerConvexity.Calculus.AffineDirectionalHessian
import PowerConvexity.Calculus.UniformQuadraticRemainder

/-! # Explicit second-derivative bounds for corrected affine first jets

Only derivatives of the same actual function occur. This quantitative estimate
is used to keep the Taylor remainder constant independent of its center.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter Metric
open scoped ContDiff Topology
namespace PowerConvexity
noncomputable section
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
local instance uahInstance1 : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance uahInstance2 : Module ℝ (E →L[ℝ] ℝ) :=
  (inferInstance : NormedSpace ℝ (E →L[ℝ] ℝ)).toModule
local instance uahInstance3 : TopologicalSpace (E →L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance uahInstance4 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance uahInstance5 : Module ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  (inferInstance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ)).toModule
local instance uahInstance6 : TopologicalSpace (E →L[ℝ] E →L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace

theorem norm_realHessian_affine_corrected_bound
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 3 f x)
    (K : E →L[ℝ] E) (c : E) (lam : ℝ) {A L B : ℝ}
    (hA : 0 ≤ A) (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hH : ‖realHessian f x‖ ≤ A)
    (hT : ‖fderiv ℝ (realHessian f) x‖ ≤ L)
    (hfield : ‖c+K x‖ ≤ B) :
    ‖realHessian (fun y => fderiv ℝ f y (c+K y)-lam*f y) x‖ ≤
      L*B+2*A*‖K‖+|lam| *A := by
  have hf2 : ContDiffAt ℝ 2 f x := hf.of_le (by norm_num)
  have hg : ContDiffAt ℝ 2 (fun y => fderiv ℝ f y (c+K y)) x :=
    (hf.fderiv_right (m := 2) (by norm_num)).clm_apply
      (contDiffAt_const.add K.contDiff.contDiffAt)
  apply ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity)
  intro p q
  have hHval (a b : E) : |realHessian f x a b| ≤ A*‖a‖*‖b‖ := by
    have hh := (realHessian f x).le_opNorm₂ a b
    rw [Real.norm_eq_abs] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hH (norm_nonneg _)) (norm_nonneg _))
  have hthird : |fderiv ℝ (realHessian f) x p q (c+K x)| ≤ L*‖p‖*‖q‖*B := by
    have h1 := (fderiv ℝ (realHessian f) x p).le_opNorm₂ q (c+K x)
    rw [Real.norm_eq_abs] at h1
    have h2 : ‖fderiv ℝ (realHessian f) x p‖ ≤ L*‖p‖ :=
      ((fderiv ℝ (realHessian f) x).le_opNorm p).trans
        (mul_le_mul_of_nonneg_right hT (norm_nonneg _))
    exact h1.trans (mul_le_mul
      (mul_le_mul_of_nonneg_right h2 (norm_nonneg _)) hfield (norm_nonneg _) (by positivity))
  have hk1 : |realHessian f x q (K p)| ≤ A*‖q‖*(‖K‖*‖p‖) :=
    (hHval q (K p)).trans (mul_le_mul_of_nonneg_left (K.le_opNorm p) (by positivity))
  have hk2 : |realHessian f x p (K q)| ≤ A*‖p‖*(‖K‖*‖q‖) :=
    (hHval p (K q)).trans (mul_le_mul_of_nonneg_left (K.le_opNorm q) (by positivity))
  have hl : |lam*realHessian f x p q| ≤ |lam| *(A*‖p‖*‖q‖) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hHval p q) (abs_nonneg _)
  rw [realHessian_sub_at hg (contDiffAt_const.mul hf2),realHessian_const_mul]
  simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,
    Real.norm_eq_abs]
  rw [realHessian_directional_affine_formula hf]
  have ha := abs_sub (fderiv ℝ (realHessian f) x p q (c+K x)+
    realHessian f x q (K p)+realHessian f x p (K q)) (lam*realHessian f x p q)
  have hb := abs_add_le (fderiv ℝ (realHessian f) x p q (c+K x)+
    realHessian f x q (K p)) (realHessian f x p (K q))
  have hc := abs_add_le (fderiv ℝ (realHessian f) x p q (c+K x)) (realHessian f x q (K p))
  nlinarith only [ha,hb,hc,hthird,hk1,hk2,hl]

end
end PowerConvexity
