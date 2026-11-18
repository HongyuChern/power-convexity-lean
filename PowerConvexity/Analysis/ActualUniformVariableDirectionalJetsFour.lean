import PowerConvexity.Calculus.AffineDirectionalHessian

/-! # Actual derivatives along a variable vector field

The Hessian difference isolates the third derivative in the fixed directional
response, so the genuine determinant first variation can eliminate it.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Filter
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus

section DifferentialIdentity
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem actual_fderiv_variable_directional_four {u : F → ℝ} {T : F → F} {x : F}
    (hu : ContDiffAt ℝ 2 u x) (hT : DifferentiableAt ℝ T x) (v : F) :
    fderiv ℝ (fun y => fderiv ℝ u y (T y)) x v =
      realHessian u x v (T x)+fderiv ℝ u x (fderiv ℝ T x v) := by
  have hdu := (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hh := hdu.hasFDerivAt.clm_apply hT.hasFDerivAt
  rw [hh.fderiv]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply,realHessian,add_comm]

theorem actual_hessian_variable_directional_four {u : F → ℝ} {T : F → F} {x : F}
    (hu : ContDiffAt ℝ 3 u x) (hT : ContDiffAt ℝ 2 T x) (v w : F) :
    realHessian (fun y => fderiv ℝ u y (T y)) x v w =
      fderiv ℝ (realHessian u) x v w (T x)+
        realHessian u x w (fderiv ℝ T x v)+
        realHessian u x v (fderiv ℝ T x w)+
        fderiv ℝ u x (fderiv ℝ (fderiv ℝ T) x v w) := by
  let p : F → ℝ := fun y => fderiv ℝ u y (T y)
  have hdu2 := hu.fderiv_right (m := 2) (by norm_num)
  have hH1 : ContDiffAt ℝ 1 (realHessian u) x :=
    hdu2.fderiv_right (m := 1) (by norm_num)
  have hp2 : ContDiffAt ℝ 2 p x := hdu2.clm_apply hT
  have hfirst : (fun y => fderiv ℝ p y w) =ᶠ[𝓝 x]
      (fun y => realHessian u y w (T y)+fderiv ℝ u y (fderiv ℝ T y w)) := by
    filter_upwards [(hu.of_le (m := 2) (by norm_num)).eventually (by norm_num),
      (hT.of_le (m := 1) (by norm_num)).eventually (by norm_num)] with y huy hTy
    exact actual_fderiv_variable_directional_four huy (hTy.differentiableAt (by norm_num)) w
  have hA := ((hp2.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasFDerivAt.clm_apply (hasFDerivAt_const w x)
  have hB1 := ((hH1.differentiableAt (by norm_num)).hasFDerivAt.clm_apply
    (hasFDerivAt_const w x)).clm_apply ((hT.differentiableAt (by norm_num)).hasFDerivAt)
  have hDT := ((hT.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasFDerivAt.clm_apply (hasFDerivAt_const w x)
  have hB2 := (hdu2.differentiableAt (by norm_num)).hasFDerivAt.clm_apply hDT
  have hB := hB1.add hB2
  change HasFDerivAt (fun y => realHessian u y w (T y)+fderiv ℝ u y (fderiv ℝ T y w)) _ x at hB
  have he := hfirst.fderiv_eq (𝕜 := ℝ)
  rw [hA.fderiv,hB.fderiv] at he
  have hev := congrArg (fun L : F →L[ℝ] ℝ => L v) he
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply,ContinuousLinearMap.zero_apply,map_zero,zero_add,add_zero] at hev
  change realHessian p x v w = _
  change realHessian p x v w = _ at hev
  simpa only [realHessian,add_assoc,add_comm,add_left_comm] using hev

theorem actual_hessian_variable_directional_difference_four {u : F → ℝ} {T : F → F} {x : F}
    (hu : ContDiffAt ℝ 3 u x) (hT : ContDiffAt ℝ 2 T x) (v w : F) :
    realHessian (fun y => fderiv ℝ u y (T y)) x v w =
      realHessian (fun y => fderiv ℝ u y (T x)) x v w+
        (realHessian u x w (fderiv ℝ T x v)+
          realHessian u x v (fderiv ℝ T x w)+
          fderiv ℝ u x (fderiv ℝ (fderiv ℝ T) x v w)) := by
  have hzero := realHessian_directional_affine_formula hu (0 : F →L[ℝ] F) (T x) v w
  simp only [ContinuousLinearMap.zero_apply,add_zero,map_zero] at hzero
  rw [actual_hessian_variable_directional_four hu hT,hzero]
  ring

end DifferentialIdentity


end PowerConvexity
