import PowerConvexity.Calculus.ComplexAffineTangentFieldTwo
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-! # Quantitative affine complex tangent fields

The normal and the field are constructed from the actual defining differential
and Hessian.  Their bounds are explicit, so the constants can be kept fixed as
the boundary center varies. No choice of an unknown Dirichlet solution occurs.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Matrix
open scoped ContDiff Topology BigOperators
namespace PowerConvexity
noncomputable section
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E]

local instance : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance : Module ℝ E := (inferInstance : InnerProductSpace ℝ E).toModule
local instance : TopologicalSpace (E →L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace

theorem exists_complex_dual_normal_with_norm (D : E →L[ℝ] ℝ) (hD : D ≠ 0) :
    ∃ n : E, D n = 1 ∧ D (Complex.I • n) = 0 ∧ ‖n‖ = ‖D‖⁻¹ := by
  let N := (InnerProductSpace.toDual ℝ E).symm D
  have hNnorm : ‖N‖ = ‖D‖ := (InnerProductSpace.toDual ℝ E).symm.norm_map _
  have hNN : D N = ‖D‖^2 := by
    rw [← InnerProductSpace.toDual_symm_apply,real_inner_self_eq_norm_sq,hNnorm]
  let ell : E →L[ℂ] ℂ := StrongDual.extendRCLike D
  have hre (v : E) : (ell v).re = D v := by
    simpa only [RCLike.re_eq_complex_re] using
      (StrongDual.re_extendRCLike_apply (𝕜 := ℂ) D v)
  have hDn : 0 < ‖D‖ := (norm_pos_iff (a := D)).mpr hD
  have hellnorm : ‖ell N‖ = ‖D‖^2 := by
    apply le_antisymm
    · have hh := StrongDual.norm_extendRCLike_bound (𝕜 := ℂ) D N
      simpa only [hNnorm,pow_two] using hh
    · calc
        ‖D‖^2 = (ell N).re := (hre N).trans hNN |>.symm
        _ ≤ |(ell N).re| := le_abs_self _
        _ ≤ ‖ell N‖ := Complex.abs_re_le_norm _
  have hz : ell N ≠ 0 := norm_ne_zero_iff.mp (by rw [hellnorm]; positivity)
  let n : E := (ell N)⁻¹ • N
  have hn : ell n = 1 := by simp [n,map_smul,hz]
  have hDn1 : D n = 1 := by
    have hh := congrArg Complex.re hn
    rwa [hre,Complex.one_re] at hh
  have hDIn : D (Complex.I • n) = 0 := by
    have hh : ell (Complex.I • n) = Complex.I := by rw [map_smul,hn,smul_eq_mul,mul_one]
    have hr := congrArg Complex.re hh
    rwa [hre,Complex.I_re] at hr
  refine ⟨n,hDn1,hDIn,?_⟩
  rw [show ‖n‖ = ‖(ell N)⁻¹‖*‖N‖ from norm_smul _ _,norm_inv,hellnorm,hNnorm]
  field_simp [ne_of_gt hDn]

theorem exists_complex_affine_tangent_linear_part_norm_two
    (e : Module.Basis (Fin 2) ℂ E) (D : E →L[ℝ] ℝ) (hD : D ≠ 0)
    (H : E →L[ℝ] E →L[ℝ] ℝ) (tau : E) :
    ∃ (K : E →L[ℂ] E) (lam : ℝ),
      (complexFieldMatrixTwo e K).trace.re = 0 ∧
      (∀ v, D (K v) = -H tau v+lam*D v) ∧
      ‖K‖ ≤ 2*‖H‖*‖tau‖/‖D‖ ∧ |lam| ≤ ‖H‖*‖tau‖/‖D‖ := by
  obtain ⟨n,hDn,hDIn,hnnorm⟩ := exists_complex_dual_normal_with_norm D hD
  let lam : ℝ := H tau n
  let phi : E →L[ℝ] ℝ := -(H tau)+lam • D
  let ell : E →L[ℂ] ℂ := StrongDual.extendRCLike phi
  let K : E →L[ℂ] E := ell.smulRight n
  have hd : 0 < ‖D‖ := (norm_pos_iff (a := D)).mpr hD
  have hlam : |lam| ≤ ‖H‖*‖tau‖/‖D‖ := by
    have hh := H.le_opNorm₂ tau n
    simpa only [lam,Real.norm_eq_abs,hnnorm,div_eq_mul_inv] using hh
  have hphin : phi n = 0 := by simp [phi,lam,hDn]
  have hphi : ‖phi‖ ≤ 2*‖H‖*‖tau‖ := by
    have h1 := norm_add_le (-(H tau)) (lam • D)
    rw [norm_neg,norm_smul,Real.norm_eq_abs] at h1
    have h2 := H.le_opNorm tau
    have h3 : |lam| * ‖D‖ ≤ ‖H‖*‖tau‖ := (le_div_iff₀ hd).mp hlam
    change ‖phi‖ ≤ _
    nlinarith only [h1,h2,h3]
  refine ⟨K,lam,?_,?_,?_,hlam⟩
  · rw [complexFieldMatrixTwo_rankOne_trace]
    have hh : (ell n).re = phi n := by
      simpa only [RCLike.re_eq_complex_re] using
        (StrongDual.re_extendRCLike_apply (𝕜 := ℂ) phi n)
    exact hh.trans hphin
  · intro v
    change D ((ell v) • n) = _
    rw [← Complex.re_add_im (ell v),add_smul,mul_smul]
    have hreal (r : ℝ) (z : E) : (r : ℂ) • z = r • z := by
      simpa only [RCLike.ofReal_eq_complex_ofReal] using
        (RCLike.real_smul_eq_coe_smul (K := ℂ) r z).symm
    rw [hreal,hreal]
    simp only [map_add,map_smul,hDn,hDIn,smul_eq_mul,mul_one,mul_zero,add_zero]
    change (ell v).re = _
    have hh : (ell v).re = phi v := by
      simpa only [RCLike.re_eq_complex_re] using
        (StrongDual.re_extendRCLike_apply (𝕜 := ℂ) phi v)
    rw [hh]
    rfl
  · change ‖ell.smulRight n‖ ≤ _
    rw [ContinuousLinearMap.norm_smulRight_apply,StrongDual.norm_extendRCLike,hnnorm]
    simpa only [div_eq_mul_inv] using
      mul_le_mul_of_nonneg_right hphi (inv_nonneg.mpr hd.le)

theorem exists_complex_affine_tangent_uniform_norm_two
    (e : Module.Basis (Fin 2) ℂ E) (D : E →L[ℝ] ℝ)
    (H : E →L[ℝ] E →L[ℝ] ℝ) (tau : E) {eta A : ℝ}
    (heta : 0 < eta) (hD : eta ≤ ‖D‖) (hH : ‖H‖ ≤ A) (htau : ‖tau‖ ≤ 1) :
    ∃ (K : E →L[ℂ] E) (lam : ℝ),
      (complexFieldMatrixTwo e K).trace.re = 0 ∧
      (∀ v, D (K v) = -H tau v+lam*D v) ∧
      ‖K‖ ≤ 2*A/eta ∧ |lam| ≤ A/eta := by
  have hDn : D ≠ 0 := (norm_pos_iff (a := D)).mp (heta.trans_le hD)
  obtain ⟨K,lam,htr,hlin,hK,hlam⟩ := exists_complex_affine_tangent_linear_part_norm_two e D hDn H tau
  have hA : 0 ≤ A := (norm_nonneg H).trans hH
  have hp : ‖H‖*‖tau‖ ≤ A := by
    have hh := mul_le_mul hH htau (norm_nonneg _) hA
    simpa only [mul_one] using hh
  refine ⟨K,lam,htr,hlin,?_,?_⟩
  · apply hK.trans
    apply div_le_div₀ (by positivity) (by nlinarith only [hp]) heta hD
  · exact hlam.trans (div_le_div₀ hA hp heta hD)

end
end PowerConvexity
