import PowerConvexity.Analysis.ActualGraphShearFour

/-! # Quantitative distortion bounds for the actual shear and inverse -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_shear_linear_norm_bound_four (N : E) (l : E →L[ℝ] ℝ) (hl : l N = 0) :
    ‖(actualShearLinearEquivFour N l hl).toContinuousLinearMap‖ ≤ 1+‖l‖*‖N‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  change ‖v+l v • N‖ ≤ _
  calc
    _ ≤ ‖v‖+‖l v • N‖ := norm_add_le _ _
    _ = ‖v‖+‖l v‖*‖N‖ := by rw [norm_smul]
    _ ≤ ‖v‖+(‖l‖*‖v‖)*‖N‖ := add_le_add (le_refl _) (mul_le_mul_of_nonneg_right (l.le_opNorm v) (norm_nonneg _))
    _ = _ := by ring

theorem actual_shear_inverse_norm_bound_four (N : E) (l : E →L[ℝ] ℝ) (hl : l N = 0) :
    ‖(actualShearLinearEquivFour N l hl).symm.toContinuousLinearMap‖ ≤ 1+‖l‖*‖N‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  change ‖v-l v • N‖ ≤ _
  calc
    _ ≤ ‖v‖+‖l v • N‖ := norm_sub_le _ _
    _ = ‖v‖+‖l v‖*‖N‖ := by rw [norm_smul]
    _ ≤ ‖v‖+(‖l‖*‖v‖)*‖N‖ := add_le_add (le_refl _) (mul_le_mul_of_nonneg_right (l.le_opNorm v) (norm_nonneg _))
    _ = _ := by ring

theorem actual_graph_shear_differential_small_four {rho : E → ℝ} {x : E}
    (hrho : ContDiffAt ℝ 2 rho x) (hzero : fderiv ℝ rho x = 0) {delta : ℝ} (hdelta : 0 < delta) :
    ∃ R > 0, ∀ y ∈ ball x R, ‖fderiv ℝ rho y‖ < delta := by
  have hc := (hrho.fderiv_right (m := 1) (by norm_num)).continuousAt
  have hnorm : Tendsto (fun y => ‖fderiv ℝ rho y‖) (𝓝 x) (𝓝 0) := by
    simpa only [hzero,norm_zero] using hc.norm.tendsto
  have he : ∀ᶠ y in 𝓝 x, ‖fderiv ℝ rho y‖ < delta := (tendsto_order.1 hnorm).2 delta hdelta
  obtain ⟨R,hR,hball⟩ := Metric.mem_nhds_iff.mp he
  exact ⟨R,hR,fun y hy => hball hy⟩

end PowerConvexity
