import PowerConvexity.Calculus.ActualThirdJetNormTwo
import PowerConvexity.Calculus.LinearProjectionJetBounds
import CHS.Calculus.HessianLocality

/-! # Exact higher derivative identities for the actual CMA variations -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Filter
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
attribute [local instance] atjInstance1 atjInstance2 atjInstance3 atjInstance4 atjInstance5 atjInstance6
local instance ahdTripleNormedGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance ahdTripleNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance ahdTripleModule : Module ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  (inferInstance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)).toModule
local instance ahdTripleTopology : TopologicalSpace (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  (ContinuousLinearMap.toNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace

theorem actual_fderiv_bilinear_entry_two
    {H : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E} (hH : DifferentiableAt ℝ H x) (v w a : E) :
    fderiv ℝ (fun y => H y v w) x a = fderiv ℝ H x a v w := by
  have hh := (hH.hasFDerivAt.clm_apply (hasFDerivAt_const v x)).clm_apply (hasFDerivAt_const w x)
  rw [hh.fderiv]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply,ContinuousLinearMap.zero_apply,map_zero,zero_add,add_zero]

theorem actual_third_jet_cycle_two
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 3 u x) (v a b : E) :
    fderiv ℝ (realHessian u) x v a b = fderiv ℝ (realHessian u) x a b v := by
  have hgrad := hu.fderiv_right (m := 2) (by norm_num)
  have hfirst : fderiv ℝ (realHessian u) x v a b =
      fderiv ℝ (realHessian u) x a v b := by
    exact congrArg (fun L : E →L[ℝ] ℝ => L b)
      ((hgrad.isSymmSndFDerivAt (by simp)).eq v a)
  have hH : DifferentiableAt ℝ (realHessian u) x :=
    (hgrad.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have he : (fun y => realHessian u y v b) =ᶠ[𝓝 x] (fun y => realHessian u y b v) := by
    filter_upwards [(hu.of_le (m := 2) (by norm_num)).eventually (by norm_num)] with y hy
    exact realHessian_symm hy v b
  have hd := congrArg (fun L : E →L[ℝ] ℝ => L a) (he.fderiv_eq (𝕜 := ℝ))
  rw [actual_fderiv_bilinear_entry_two hH v b a,actual_fderiv_bilinear_entry_two hH b v a] at hd
  exact hfirst.trans hd

theorem actual_Hessian_directional_differentiation_two
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 3 u x) (v a b : E) :
    fderiv ℝ (fun y => realHessian u y a b) x v =
      realHessian (fun y => fderiv ℝ u y v) x a b := by
  have hH : DifferentiableAt ℝ (realHessian u) x :=
    ((hu.fderiv_right (m := 2) (by norm_num)).fderiv_right
      (m := 1) (by norm_num)).differentiableAt (by norm_num)
  exact (actual_fderiv_bilinear_entry_two hH a b v).trans
    ((actual_third_jet_cycle_two hu v a b).trans
      (actual_third_jet_directional_identity_two hu v a b).symm)

theorem actual_second_variation_Hessian_commute_two
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 4 u x) (v w a b : E) :
    fderiv ℝ (fun y => realHessian (fun z => fderiv ℝ u z v) y a b) x w =
      realHessian (fun y => realHessian u y w v) x a b := by
  have hp : ContDiffAt ℝ 3 (fun y => fderiv ℝ u y v) x :=
    (hu.fderiv_right (m := 3) (by norm_num)).clm_apply contDiffAt_const
  have he : (fun y => fderiv ℝ (fun z => fderiv ℝ u z v) y w) =ᶠ[𝓝 x]
      (fun y => realHessian u y w v) := by
    filter_upwards [(hu.of_le (m := 2) (by norm_num)).eventually (by norm_num)] with y hy
    simpa only [ContinuousLinearMap.zero_apply,map_zero,add_zero] using
      fderiv_directional_affine_apply hy (0 : E →L[ℝ] E) v w
  rw [actual_Hessian_directional_differentiation_two hp w a b,
    realHessian_eq_of_eventuallyEq he]

theorem actual_fourth_jet_scalar_identity_two
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 4 u x) (v w a b : E) :
    realHessian (fun y => realHessian u y v w) x a b =
      fderiv ℝ (fderiv ℝ (realHessian u)) x a b v w := by
  have hH : ContDiffAt ℝ 2 (realHessian u) x :=
    (hu.fderiv_right (m := 3) (by norm_num)).fderiv_right (m := 2) (by norm_num)
  let ev : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.apply ℝ ℝ w).comp (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) v)
  change realHessian (fun y => ev (realHessian u y)) x a b = _
  rw [realHessian_linear_projection_eq hH ev]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.compL_apply,ev,
    ContinuousLinearMap.apply_apply]

end PowerConvexity
