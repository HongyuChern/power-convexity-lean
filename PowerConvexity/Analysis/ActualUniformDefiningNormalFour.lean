import PowerConvexity.Analysis.ActualUniformDefiningTangentialFieldFour
import PowerConvexity.Analysis.CompactPositiveScaling
import Mathlib.Analysis.InnerProductSpace.Dual

/-! # A genuine common defining-normal margin and its unit field -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def actualDefiningUnitNormalFour (g : E → ℝ) (c : E) : E :=
  ‖fderiv ℝ g c‖⁻¹ • (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ g c)

theorem actual_defining_unit_normal_four {g : E → ℝ} {c : E} (hD : fderiv ℝ g c≠0) :
    ‖actualDefiningUnitNormalFour g c‖=1 ∧
      fderiv ℝ g c (actualDefiningUnitNormalFour g c)=‖fderiv ℝ g c‖ ∧
      ∀ v : E, fderiv ℝ g c v=‖fderiv ℝ g c‖*inner ℝ (actualDefiningUnitNormalFour g c) v := by
  let V := (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ g c)
  have hV : ‖V‖=‖fderiv ℝ g c‖ := (InnerProductSpace.toDual ℝ E).symm.norm_map _
  have hpos : 0 < ‖fderiv ℝ g c‖ := norm_pos_iff.mpr hD
  have hpair (v : E) : inner ℝ V v=fderiv ℝ g c v := InnerProductSpace.toDual_symm_apply
  have hnorm : ‖actualDefiningUnitNormalFour g c‖=1 := by
    rw [actualDefiningUnitNormalFour,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hpos),hV,
      inv_mul_cancel₀ hpos.ne']
  have hcov (v : E) : fderiv ℝ g c v=‖fderiv ℝ g c‖*inner ℝ (actualDefiningUnitNormalFour g c) v := by
    change fderiv ℝ g c v=‖fderiv ℝ g c‖*inner ℝ (‖fderiv ℝ g c‖⁻¹ • V) v
    rw [real_inner_smul_left,hpair,← mul_assoc,mul_inv_cancel₀ hpos.ne',one_mul]
  refine ⟨hnorm,?_,hcov⟩
  rw [hcov,real_inner_self_eq_norm_sq,hnorm,one_pow,mul_one]

theorem actual_uniform_defining_normal_margin_four
    {U : Set E} (hK : IsCompact (closure U)) {g : E → ℝ} (hg : ContDiff ℝ 2 g)
    (hDg : ∀ c ∈ frontier U, fderiv ℝ g c≠0) :
    ∃ delta > 0, ∀ c ∈ frontier U, delta ≤ ‖fderiv ℝ g c‖ := by
  have hfront : IsCompact (frontier U) := hK.of_isClosed_subset isClosed_frontier frontier_subset_closure
  have hcont : Continuous (fun c => ‖fderiv ℝ g c‖) := by
    apply continuous_iff_continuousAt.mpr
    intro c
    exact ((hg.contDiffAt (x := c)).fderiv_right (m := 1) (by norm_num)).continuousAt.norm
  obtain ⟨a,ha,hmargin⟩ := exists_uniform_square_scaling_gt_one hfront hcont
    (fun c hc => norm_pos_iff.mpr (hDg c hc))
  have ha0 : 0 < a := by linarith
  refine ⟨1/a^2,by positivity,?_⟩
  intro c hc
  apply (div_le_iff₀ (sq_pos_of_pos ha0)).mpr
  simpa only [mul_comm] using (hmargin c hc).le

end PowerConvexity
