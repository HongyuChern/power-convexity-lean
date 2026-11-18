import PowerConvexity.Analysis.ActualUniformClosureMixedModulusFour

/-! # Actual closure-pair tangential response differences control mixed Hessians

Both points may lie on the true boundary. The variable-field correction is
retained, and the statement is purely about the same actual closure jet.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem actual_closure_pair_mixed_covector_difference_four
    {U : Set E} {u : E → ℝ} (J : ClosureC2Jet u U)
    {T : E → E} {x c : E} :
    ‖(J.hessian x-J.hessian c).flip (T c)‖ ≤
      ‖actualClosureTangentialDerivativeFour J T x-
        actualClosureTangentialDerivativeFour J T c‖+
      ‖J.hessian x‖*‖T x-T c‖+
      ‖J.derivative x-J.derivative c‖*‖fderiv ℝ T c‖+
      ‖J.derivative x‖*‖fderiv ℝ T x-fderiv ℝ T c‖ := by
  have he : (J.hessian x-J.hessian c).flip (T c)=
      ((actualClosureTangentialDerivativeFour J T x-
        actualClosureTangentialDerivativeFour J T c)-
        (J.hessian x).flip (T x-T c))-
        (J.derivative x-J.derivative c).comp (fderiv ℝ T c)-
        (J.derivative x).comp (fderiv ℝ T x-fderiv ℝ T c) := by
    simp only [actualClosureTangentialDerivativeFour]
    apply ContinuousLinearMap.ext
    intro v
    simp only [ContinuousLinearMap.flip_apply,ContinuousLinearMap.comp_apply,
      _root_.add_apply,_root_.sub_apply,map_sub]
    ring
  rw [he]
  have hH : ‖(J.hessian x).flip (T x-T c)‖ ≤ ‖J.hessian x‖*‖T x-T c‖ := by
    simpa only [ContinuousLinearMap.opNorm_flip] using (J.hessian x).flip.le_opNorm (T x-T c)
  exact (norm_sub_le _ _).trans (add_le_add
    ((norm_sub_le _ _).trans (add_le_add
      ((norm_sub_le _ _).trans (add_le_add le_rfl hH)) (ContinuousLinearMap.opNorm_comp_le _ _)))
    (ContinuousLinearMap.opNorm_comp_le _ _))

theorem actual_closure_pair_mixed_covector_modulus_four
    {U : Set E} {u : E → ℝ} (J : ClosureC2Jet u U)
    {T : E → E} {x c e : E} {lam delta eps G H D K d : ℝ}
    (hd : 0 < delta) (hlam : delta ≤ lam) (hTc : T c=lam • e)
    (hG : 0 ≤ G) (hH : 0 ≤ H) (hD : 0 ≤ D) (hdist : 0 ≤ d)
    (hresponse : ‖actualClosureTangentialDerivativeFour J T x-
      actualClosureTangentialDerivativeFour J T c‖ ≤ eps)
    (hHu : ‖J.hessian x‖ ≤ H) (hDu : ‖J.derivative x‖ ≤ G)
    (hfield : ‖T x-T c‖ ≤ D*d) (hDf : ‖fderiv ℝ T c‖ ≤ D)
    (hJlip : ‖J.derivative x-J.derivative c‖ ≤ H*d)
    (hfieldD : ‖fderiv ℝ T x-fderiv ℝ T c‖ ≤ K*d) :
    ‖(J.hessian x-J.hessian c).flip e‖ ≤ (eps+(2*H*D+G*K)*d)/delta := by
  have hlim := actual_closure_pair_mixed_covector_difference_four (T := T) (x := x) (c := c) J
  have hbound : ‖(J.hessian x-J.hessian c).flip (T c)‖ ≤ eps+(2*H*D+G*K)*d := by
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
    (ContinuousLinearMap.opNorm_nonneg ((J.hessian x-J.hessian c).flip e))
  nlinarith

end PowerConvexity
