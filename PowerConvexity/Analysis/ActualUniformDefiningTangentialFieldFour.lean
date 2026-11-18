import PowerConvexity.Analysis.ActualUniformClosureTangentialResponseFour
import PowerConvexity.Calculus.RegularDefiningBoundaryChart
import Mathlib.Analysis.Normed.Operator.Bilinear

/-! # Actual global tangential fields from the defining function

The field Df(N)e-Df(e)N is tangent to every regular level. Its C2 bounds use
only the C3 norm of the fixed defining function. Its actual closure response
has zero boundary trace by the genuine regular-level chart, independently of
the density in the nonlinear equation.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus

section Fields
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
local instance udtf1 : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance udtf2 : Module ℝ (E →L[ℝ] ℝ) :=
  (inferInstance : NormedSpace ℝ (E →L[ℝ] ℝ)).toModule
local instance udtf3 : TopologicalSpace (E →L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance udtf4 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance udtf5 : Module ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  (inferInstance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ)).toModule
local instance udtf6 : TopologicalSpace (E →L[ℝ] E →L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace

def actualDefiningTangentialOperatorFour (e N : E) : (E →L[ℝ] ℝ) →L[ℝ] E :=
  (ContinuousLinearMap.apply ℝ ℝ N).smulRight e-
    (ContinuousLinearMap.apply ℝ ℝ e).smulRight N

def actualDefiningTangentialFieldFour (f : E → ℝ) (e N : E) (x : E) : E :=
  actualDefiningTangentialOperatorFour e N (fderiv ℝ f x)

theorem actual_defining_tangential_field_value_four (f : E → ℝ) (e N x : E) :
    actualDefiningTangentialFieldFour f e N x = fderiv ℝ f x N • e-fderiv ℝ f x e • N := rfl

theorem actual_defining_tangential_field_tangent_four (f : E → ℝ) (e N x : E) :
    fderiv ℝ f x (actualDefiningTangentialFieldFour f e N x)=0 := by
  rw [actual_defining_tangential_field_value_four]
  simp only [map_sub,map_smul,smul_eq_mul]
  ring

theorem actual_defining_tangential_operator_norm_four (e N : E) :
    ‖actualDefiningTangentialOperatorFour e N‖ ≤ 2*‖e‖*‖N‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro l
  change ‖l N • e-l e • N‖ ≤ _
  calc
    _ ≤ ‖l N • e‖+‖l e • N‖ := norm_sub_le _ _
    _ = |l N| * ‖e‖+|l e| * ‖N‖ := by rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs]
    _ ≤ (‖l‖*‖N‖)*‖e‖+(‖l‖*‖e‖)*‖N‖ :=
      add_le_add (mul_le_mul_of_nonneg_right (l.le_opNorm N) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (l.le_opNorm e) (norm_nonneg _))
    _ = _ := by ring

theorem actual_defining_tangential_field_norm_four (f : E → ℝ) (e N x : E) :
    ‖actualDefiningTangentialFieldFour f e N x‖ ≤ (2*‖e‖*‖N‖)*‖fderiv ℝ f x‖ :=
  ((actualDefiningTangentialOperatorFour e N).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (actual_defining_tangential_operator_norm_four e N) (norm_nonneg _))

theorem actual_defining_tangential_field_regular_four {U : Set E} (hU : IsOpen U)
    {f : E → ℝ} (hf : ContDiffOn ℝ 3 f U) (e N : E) :
    ContDiffOn ℝ 2 (actualDefiningTangentialFieldFour f e N) U :=
  (actualDefiningTangentialOperatorFour e N).contDiff.comp_contDiffOn
    (hf.fderiv_of_isOpen hU (m := 2) (by norm_num))

theorem actual_defining_tangential_field_fderiv_four {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (e N : E) :
    fderiv ℝ (actualDefiningTangentialFieldFour f e N) x=
      (actualDefiningTangentialOperatorFour e N).comp (realHessian f x) := by
  exact ((actualDefiningTangentialOperatorFour e N).hasFDerivAt.comp x
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt).fderiv

theorem actual_defining_tangential_field_fderiv_bound_four {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (e N : E) :
    ‖fderiv ℝ (actualDefiningTangentialFieldFour f e N) x‖ ≤
      (2*‖e‖*‖N‖)*‖realHessian f x‖ := by
  rw [actual_defining_tangential_field_fderiv_four hf]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right (actual_defining_tangential_operator_norm_four e N) (norm_nonneg _))

theorem actual_defining_tangential_field_second_fderiv_four {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 3 f x) (e N : E) :
    fderiv ℝ (fderiv ℝ (actualDefiningTangentialFieldFour f e N)) x=
      (ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E
        (actualDefiningTangentialOperatorFour e N)).comp (fderiv ℝ (realHessian f) x) := by
  have he : fderiv ℝ (actualDefiningTangentialFieldFour f e N) =ᶠ[𝓝 x]
      (fun y => (actualDefiningTangentialOperatorFour e N).comp (realHessian f y)) := by
    filter_upwards [(hf.of_le (m := 2) (by norm_num)).eventually (by norm_num)] with y hy
    exact actual_defining_tangential_field_fderiv_four hy e N
  rw [he.fderiv_eq]
  exact ((ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E
    (actualDefiningTangentialOperatorFour e N)).hasFDerivAt.comp x
      ((((hf.fderiv_right (m := 2) (by norm_num)).fderiv_right
        (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt)).fderiv

theorem actual_defining_tangential_field_second_fderiv_bound_four {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 3 f x) (e N : E) :
    ‖fderiv ℝ (fderiv ℝ (actualDefiningTangentialFieldFour f e N)) x‖ ≤
      (2*‖e‖*‖N‖)*‖fderiv ℝ (realHessian f) x‖ := by
  rw [actual_defining_tangential_field_second_fderiv_four hf]
  have hcomp : ‖ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E
      (actualDefiningTangentialOperatorFour e N)‖ ≤ 2*‖e‖*‖N‖ := by
    apply le_trans ?_ (actual_defining_tangential_operator_norm_four e N)
    exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
      (fun H => ContinuousLinearMap.opNorm_comp_le _ H)
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right hcomp (norm_nonneg _))

end Fields

section ActualBoundaryTrace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem actual_closure_tangential_response_zero_of_defining_four
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U)
    {u : E → ℝ} (hu : DifferentiableOn ℝ u U) (J : ClosureC2Jet u U)
    (hb : ∀ x ∈ frontier U, u x=0) {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hfx : f x=0) (hDf : fderiv ℝ f x≠0)
    (hdef : ∀ᶠ z in 𝓝 x, z∈U ↔ f z<0) {T : E → E}
    (htan : fderiv ℝ f x (T x)=0) :
    actualClosureTangentialResponseFour J T x=0 := by
  obtain ⟨gamma,V,hV,h0,hgamma0,hgamma,hbdy,_,hkernel⟩ :=
    exists_contDiff_defining_boundary_chart hU hf hfx hDf hdef
  have hh := actual_closure_tangential_response_zero_of_chart_four hU hconv hu J hb hV
    (hgamma.differentiableOn (by norm_num)) hbdy h0 (T x)
    (by rw [hgamma0,hkernel _ htan])
  simpa only [hgamma0] using hh

theorem actual_defining_tangential_response_zero_four
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U)
    {u : E → ℝ} (hu : DifferentiableOn ℝ u U) (J : ClosureC2Jet u U)
    (hb : ∀ x ∈ frontier U, u x=0) {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hfx : f x=0) (hDf : fderiv ℝ f x≠0)
    (hdef : ∀ᶠ z in 𝓝 x, z∈U ↔ f z<0) (e N : E) :
    actualClosureTangentialResponseFour J (actualDefiningTangentialFieldFour f e N) x=0 :=
  actual_closure_tangential_response_zero_of_defining_four hU hconv hu J hb hf hfx hDf hdef
    (actual_defining_tangential_field_tangent_four f e N x)

end ActualBoundaryTrace
end PowerConvexity
