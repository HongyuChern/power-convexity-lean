import PowerConvexity.Calculus.DirectionalDerivativeBoundaryMaximum

/-! # Genuine derivatives along an affine real vector field

All first, second and third derivatives below belong to the same actual
potential. These identities prepare the affine holomorphic boundary fields.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Filter
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fderiv_directional_affine_apply
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x)
    (K : E →L[ℝ] E) (c q : E) :
    fderiv ℝ (fun y => fderiv ℝ u y (c+K y)) x q =
      realHessian u x q (c+K x)+fderiv ℝ u x (K q) := by
  have hdu := (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hT : HasFDerivAt (fun y => c+K y) K x := K.hasFDerivAt.const_add c
  have hh := hdu.hasFDerivAt.clm_apply hT
  rw [hh.fderiv]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply,realHessian,add_comm]

theorem realHessian_directional_affine_formula
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 3 u x)
    (K : E →L[ℝ] E) (c p q : E) :
    realHessian (fun y => fderiv ℝ u y (c+K y)) x p q =
      fderiv ℝ (realHessian u) x p q (c+K x)+
        realHessian u x q (K p)+realHessian u x p (K q) := by
  let f : E → ℝ := fun y => fderiv ℝ u y (c+K y)
  have hdu2 := hu.fderiv_right (m := 2) (by norm_num)
  have hH1 : ContDiffAt ℝ 1 (realHessian u) x :=
    hdu2.fderiv_right (m := 1) (by norm_num)
  have hf2 : ContDiffAt ℝ 2 f x :=
    hdu2.clm_apply (contDiffAt_const.add K.contDiff.contDiffAt)
  have hT : HasFDerivAt (fun y => c+K y) K x := K.hasFDerivAt.const_add c
  have hfirst : (fun y => fderiv ℝ f y q) =ᶠ[𝓝 x]
      (fun y => realHessian u y q (c+K y)+fderiv ℝ u y (K q)) := by
    filter_upwards [(hu.of_le (m := 2) (by norm_num)).eventually (by norm_num)] with y hy
    exact fderiv_directional_affine_apply hy K c q
  have hA := ((hf2.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasFDerivAt.clm_apply (hasFDerivAt_const q x)
  have hB1 := ((hH1.differentiableAt (by norm_num)).hasFDerivAt.clm_apply
    (hasFDerivAt_const q x)).clm_apply hT
  have hB2 := (hdu2.differentiableAt (by norm_num)).hasFDerivAt.clm_apply
    (hasFDerivAt_const (K q) x)
  have hB := hB1.add hB2
  change HasFDerivAt (fun y => realHessian u y q (c+K y)+fderiv ℝ u y (K q)) _ x at hB
  have he := hfirst.fderiv_eq (𝕜 := ℝ)
  rw [hA.fderiv,hB.fderiv] at he
  have hep := congrArg (fun L : E →L[ℝ] ℝ => L p) he
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply,ContinuousLinearMap.zero_apply,map_zero,zero_add,add_zero] at hep
  change realHessian f x p q = _
  change realHessian f x p q = _ at hep
  simpa only [realHessian,add_assoc,add_comm,add_left_comm] using hep

theorem realHessian_directional_affine_difference
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 3 u x)
    (K : E →L[ℝ] E) (c p q : E) :
    realHessian (fun y => fderiv ℝ u y (c+K y)) x p q =
      realHessian (fun y => fderiv ℝ u y (c+K x)) x p q+
        realHessian u x q (K p)+realHessian u x p (K q) := by
  have hzero := realHessian_directional_affine_formula hu (0 : E →L[ℝ] E) (c+K x) p q
  simp only [ContinuousLinearMap.zero_apply,add_zero,map_zero] at hzero
  rw [realHessian_directional_affine_formula hu K c p q,hzero]

end PowerConvexity
