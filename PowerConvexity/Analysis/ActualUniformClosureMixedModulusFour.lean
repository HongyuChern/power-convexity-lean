import PowerConvexity.Analysis.ActualUniformTangentialGradientModulusFour

/-! # The actual response derivative controls the actual mixed closure Hessian

The variable-field correction is retained at both points. The remaining
errors use only the already known first-jet Lipschitz bound and the C2 bound
of the fixed field. The Hessian modulus is a conclusion of the estimate.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def actualClosureTangentialDerivativeFour {U : Set E} {u : E → ℝ}
    (J : ClosureC2Jet u U) (T : E → E) (x : E) : E →L[ℝ] ℝ :=
  (J.hessian x).flip (T x)+(J.derivative x).comp (fderiv ℝ T x)

theorem actual_closure_tangential_response_hasFDerivWithinAt_four
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U)
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U)
    {T : E → E} {x : E} (hx : x ∈ closure U) (hT : DifferentiableAt ℝ T x) :
    HasFDerivWithinAt (actualClosureTangentialResponseFour J T)
      (actualClosureTangentialDerivativeFour J T x) (closure U) x := by
  have hh := (closureJet_derivative_hasFDerivWithinAt hU hconv hu J hx).clm_apply
    hT.hasFDerivAt.hasFDerivWithinAt
  apply HasFDerivWithinAt.of_isLittleO
  simpa only [actualClosureTangentialResponseFour,actualClosureTangentialDerivativeFour,add_comm] using
    hh.isLittleO

theorem actual_closure_tangential_response_fderiv_four
    {U : Set E} (hU : IsOpen U) {u : E → ℝ} (J : ClosureC2Jet u U)
    {T : E → E} {x : E} (hx : x ∈ U)
    (hu : ContDiffAt ℝ 2 u x) (hT : DifferentiableAt ℝ T x) :
    fderiv ℝ (actualClosureTangentialResponseFour J T) x=
      actualClosureTangentialDerivativeFour J T x := by
  rw [(actual_closure_tangential_response_eventually_eq_four hU J T hx).fderiv_eq,
    actual_variable_directional_fderiv_operator_four hu hT]
  rw [actualClosureTangentialDerivativeFour,J.hessian_eq hx,J.derivative_eq hx]
  rfl

theorem actual_mixed_closure_covector_difference_four
    {U : Set E} (hU : IsOpen U) {u : E → ℝ} (J : ClosureC2Jet u U)
    {T : E → E} {x c : E} (hx : x ∈ U)
    (hu : ContDiffAt ℝ 2 u x) (hT : DifferentiableAt ℝ T x) :
    ‖(realHessian u x-J.hessian c).flip (T c)‖ ≤
      ‖fderiv ℝ (actualClosureTangentialResponseFour J T) x-
        actualClosureTangentialDerivativeFour J T c‖+
      ‖realHessian u x‖*‖T x-T c‖+
      ‖fderiv ℝ u x-J.derivative c‖*‖fderiv ℝ T c‖+
      ‖fderiv ℝ u x‖*‖fderiv ℝ T x-fderiv ℝ T c‖ := by
  have hD : fderiv ℝ (actualClosureTangentialResponseFour J T) x=
      (realHessian u x).flip (T x)+(fderiv ℝ u x).comp (fderiv ℝ T x) := by
    rw [(actual_closure_tangential_response_eventually_eq_four hU J T hx).fderiv_eq,
      actual_variable_directional_fderiv_operator_four hu hT]
  have he : (realHessian u x-J.hessian c).flip (T c)=
      ((fderiv ℝ (actualClosureTangentialResponseFour J T) x-
        actualClosureTangentialDerivativeFour J T c)-
        (realHessian u x).flip (T x-T c))-
        (fderiv ℝ u x-J.derivative c).comp (fderiv ℝ T c)-
        (fderiv ℝ u x).comp (fderiv ℝ T x-fderiv ℝ T c) := by
    rw [hD,actualClosureTangentialDerivativeFour]
    apply ContinuousLinearMap.ext
    intro v
    simp only [ContinuousLinearMap.flip_apply,ContinuousLinearMap.comp_apply,
      _root_.add_apply,_root_.sub_apply,map_sub]
    ring
  rw [he]
  have hH : ‖(realHessian u x).flip (T x-T c)‖ ≤ ‖realHessian u x‖*‖T x-T c‖ := by
    simpa only [ContinuousLinearMap.opNorm_flip] using (realHessian u x).flip.le_opNorm (T x-T c)
  exact (norm_sub_le _ _).trans (add_le_add
    ((norm_sub_le _ _).trans (add_le_add
      ((norm_sub_le _ _).trans (add_le_add le_rfl hH)) (ContinuousLinearMap.opNorm_comp_le _ _)))
    (ContinuousLinearMap.opNorm_comp_le _ _))

theorem actual_mixed_closure_covector_modulus_four
    {U : Set E} (hU : IsOpen U) {u : E → ℝ} (J : ClosureC2Jet u U)
    {T : E → E} {x c e : E} {lam delta eps G H D K d : ℝ}
    (hx : x ∈ U) (hu : ContDiffAt ℝ 2 u x) (hT : DifferentiableAt ℝ T x)
    (hd : 0 < delta) (hlam : delta ≤ lam) (hTc : T c=lam • e)
    (hG : 0 ≤ G) (hH : 0 ≤ H) (hD : 0 ≤ D) (hdist : 0 ≤ d)
    (hresponse : ‖fderiv ℝ (actualClosureTangentialResponseFour J T) x-
      actualClosureTangentialDerivativeFour J T c‖ ≤ eps)
    (hHu : ‖realHessian u x‖ ≤ H) (hDu : ‖fderiv ℝ u x‖ ≤ G)
    (hfield : ‖T x-T c‖ ≤ D*d) (hDf : ‖fderiv ℝ T c‖ ≤ D)
    (hJlip : ‖fderiv ℝ u x-J.derivative c‖ ≤ H*d)
    (hfieldD : ‖fderiv ℝ T x-fderiv ℝ T c‖ ≤ K*d) :
    ‖(realHessian u x-J.hessian c).flip e‖ ≤ (eps+(2*H*D+G*K)*d)/delta := by
  have hlim := actual_mixed_closure_covector_difference_four (c := c) hU J hx hu hT
  have hbound : ‖(realHessian u x-J.hessian c).flip (T c)‖ ≤ eps+(2*H*D+G*K)*d := by
    apply hlim.trans
    calc
      _ ≤ eps+H*(D*d)+(H*d)*D+G*(K*d) := add_le_add
        (add_le_add (add_le_add hresponse (mul_le_mul hHu hfield (norm_nonneg _) hH))
          (mul_le_mul hJlip hDf (norm_nonneg _) (mul_nonneg hH hdist)))
        (mul_le_mul hDu hfieldD (norm_nonneg _) hG)
      _ = _ := by ring
  rw [hTc,map_smul,norm_smul,Real.norm_eq_abs,abs_of_pos (hd.trans_le hlam)] at hbound
  apply (le_div_iff₀ hd).mpr
  have hmul := mul_le_mul_of_nonneg_right hlam
    (ContinuousLinearMap.opNorm_nonneg ((realHessian u x-J.hessian c).flip e))
  nlinarith

end PowerConvexity
