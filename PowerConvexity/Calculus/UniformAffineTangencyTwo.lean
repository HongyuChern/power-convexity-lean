import PowerConvexity.Calculus.QuantitativeComplexAffineTangentTwo
import PowerConvexity.Calculus.UniformAffineHessianBound
import PowerConvexity.Calculus.LocalThirdDerivativeBounds

/-! # A common quadratic tangency bound for moving boundary centers

The centers and the unit tangent directions vary, but one radius, one quadratic
constant, and one affine-linear norm bound are chosen first. All derivatives
are actual derivatives of the given defining function.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
open Set Filter Metric Matrix
open scoped ContDiff Topology BigOperators
namespace PowerConvexity
noncomputable section
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E]
local instance uatInstance1 : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance uatInstance2 : Module ℝ E := (inferInstance : InnerProductSpace ℝ E).toModule
local instance uatInstance3 : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance uatInstance4 : Module ℝ (E →L[ℝ] ℝ) :=
  (inferInstance : NormedSpace ℝ (E →L[ℝ] ℝ)).toModule
local instance uatInstance5 : TopologicalSpace (E →L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance uatInstance6 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance uatInstance7 : Module ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  (inferInstance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ)).toModule
local instance uatInstance8 : TopologicalSpace (E →L[ℝ] E →L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace

theorem affine_complex_tangency_uniform_on_closedBall_two
    (e : Module.Basis (Fin 2) ℂ E) {f : E → ℝ} {p : E} {R eta A L : ℝ}
    (hR : 0 ≤ R) (heta : 0 < eta) (hA : 0 ≤ A) (hL : 0 ≤ L)
    (hf : ∀ y ∈ closedBall p R, ContDiffAt ℝ 3 f y)
    (hH : ∀ y ∈ closedBall p R, ‖realHessian f y‖ ≤ A)
    (hT : ∀ y ∈ closedBall p R, ‖fderiv ℝ (realHessian f) y‖ ≤ L) :
    ∃ C > 0, ∀ x ∈ closedBall p R, eta ≤ ‖fderiv ℝ f x‖ → f x = 0 →
      ∀ tau : E, ‖tau‖ ≤ 1 → fderiv ℝ f x tau = 0 →
      ∃ (K : E →L[ℂ] E) (c : E),
        (complexFieldMatrixTwo e K).trace.re = 0 ∧ c+K x = tau ∧ ‖K‖ ≤ 2*A/eta ∧
        ∀ y ∈ closedBall p R, f y = 0 →
          |fderiv ℝ f y (c+K y)| ≤ C*‖y-x‖^2 := by
  let K0 : ℝ := 2*A/eta
  let L0 : ℝ := A/eta
  let B : ℝ := 1+K0*(2*R)
  let C : ℝ := L*B+2*A*K0+L0*A+1
  have hK0 : 0 ≤ K0 := by dsimp [K0]; positivity
  have hL0 : 0 ≤ L0 := by dsimp [L0]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro x hx hDx hfx tau htau htangent
  obtain ⟨K,lam,htrace,hlin,hK,hlam⟩ := exists_complex_affine_tangent_uniform_norm_two
    e (fderiv ℝ f x) (realHessian f x) tau heta hDx (hH x hx) htau
  let c : E := tau-K x
  have hcx : c+K x = tau := sub_add_cancel _ _
  let g : E → ℝ := fun y => fderiv ℝ f y (c+K y)
  let r : E → ℝ := fun y => g y-lam*f y
  have hg (y : E) (hy : y ∈ closedBall p R) : ContDiffAt ℝ 2 g y :=
    ((hf y hy).fderiv_right (m := 2) (by norm_num)).clm_apply
      (contDiffAt_const.add (K.restrictScalars ℝ).contDiff.contDiffAt)
  have hr (y : E) (hy : y ∈ closedBall p R) : ContDiffAt ℝ 2 r y :=
    (hg y hy).sub (contDiffAt_const.mul ((hf y hy).of_le (by norm_num)))
  have hrx : r x = 0 := by simp only [r,g,hcx,htangent,hfx,mul_zero,sub_self]
  have hrd : fderiv ℝ r x = 0 := by
    have hd := ((hg x hx).differentiableAt (by norm_num)).hasFDerivAt.sub
      (((hf x hx).differentiableAt (by norm_num)).hasFDerivAt.const_mul lam)
    change HasFDerivAt r _ x at hd
    rw [hd.fderiv]
    ext v
    simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.zero_apply,smul_eq_mul]
    change fderiv ℝ g x v-lam*fderiv ℝ f x v = 0
    rw [show fderiv ℝ g x v = realHessian f x v (c+K x)+fderiv ℝ f x (K v) from
      fderiv_directional_affine_apply ((hf x hx).of_le (by norm_num)) (K.restrictScalars ℝ) c v,
      hcx,hlin v,realHessian_symm ((hf x hx).of_le (by norm_num)) v tau]
    ring
  have hfield (y : E) (hy : y ∈ closedBall p R) : ‖c+K y‖ ≤ B := by
    have hd : ‖y-x‖ ≤ 2*R := by
      have hh := (dist_triangle y p x).trans
        (add_le_add (mem_closedBall.mp hy) (by simpa only [dist_comm] using mem_closedBall.mp hx))
      simpa only [dist_eq_norm,two_mul] using hh
    have he : c+K y = tau+K (y-x) := by dsimp [c]; simp only [map_sub]; abel
    rw [he]
    calc
      ‖tau+K (y-x)‖ ≤ ‖tau‖+‖K (y-x)‖ := norm_add_le _ _
      _ ≤ 1+K0*(2*R) := add_le_add htau
        ((K.le_opNorm (y-x)).trans (mul_le_mul hK hd (norm_nonneg _) hK0))
      _ = B := rfl
  have hRH (y : E) (hy : y ∈ closedBall p R) : ‖realHessian r y‖ ≤ C := by
    have hh := norm_realHessian_affine_corrected_bound (hf y hy)
      (K.restrictScalars ℝ) c lam hA hL hB (hH y hy) (hT y hy) (hfield y hy)
    change ‖realHessian r y‖ ≤ L*B+2*A*‖K.restrictScalars ℝ‖+|lam| * A at hh
    rw [ContinuousLinearMap.norm_restrictScalars] at hh
    have hk := mul_le_mul_of_nonneg_left hK (by positivity : 0 ≤ 2*A)
    have hl := mul_le_mul_of_nonneg_right hlam hA
    dsimp only [C,K0,L0] at *
    linarith only [hh,hk,hl]
  refine ⟨K,c,htrace,hcx,hK,?_⟩
  intro y hy hfy
  have hh := quadratic_remainder_on_closedBall_of_Hessian_bound hC.le hr hRH hx hy
  simpa only [hrx,hrd,ContinuousLinearMap.zero_apply,sub_zero,r,g,hfy,mul_zero] using hh

theorem exists_local_uniform_affine_complex_tangency_two
    (e : Module.Basis (Fin 2) ℂ E) {f : E → ℝ} {p : E}
    (hf : ContDiffAt ℝ 3 f p) (hDf : fderiv ℝ f p ≠ 0) :
    ∃ C > 0, ∃ M ≥ 0, ∃ R > 0,
      ∀ x ∈ closedBall p R, f x = 0 →
        ∀ tau : E, ‖tau‖ ≤ 1 → fderiv ℝ f x tau = 0 →
        ∃ (K : E →L[ℂ] E) (c : E),
          (complexFieldMatrixTwo e K).trace.re = 0 ∧ c+K x = tau ∧ ‖K‖ ≤ M ∧
          ∀ y ∈ closedBall p R, f y = 0 →
            |fderiv ℝ f y (c+K y)| ≤ C*‖y-x‖^2 := by
  obtain ⟨eta,heta,A,hA,L,hL,R,hR,hbounds⟩ :=
    exists_local_uniform_third_derivative_bounds hf hDf
  obtain ⟨C,hC,hquad⟩ := affine_complex_tangency_uniform_on_closedBall_two e hR.le heta hA.le hL.le
    (fun y hy => (hbounds y hy).1)
    (fun y hy => (hbounds y hy).2.2.1)
    (fun y hy => (hbounds y hy).2.2.2)
  refine ⟨C,hC,2*A/eta,by positivity,R,hR,?_⟩
  intro x hx hfx tau htau htangent
  exact hquad x hx (hbounds x hx).2.1 hfx tau htau htangent

end
end PowerConvexity
