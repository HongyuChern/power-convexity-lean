import PowerConvexity.Calculus.RealHessianRules
import Mathlib.Analysis.Calculus.MeanValue

/-! # A local quadratic remainder bound from actual C2 regularity -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open Set Metric Filter
open scoped ContDiff Topology
namespace PowerConvexity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_local_quadratic_remainder_bound {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) :
    ∃ C > 0, ∃ δ > 0, ∀ y : E, ‖y-x‖ < δ →
      |f y-f x-fderiv ℝ f x (y-x)| ≤ C*‖y-x‖^2 := by
  have hD : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  obtain ⟨C,hC,hDbound⟩ := hD.isBigO_sub.exists_pos
  have hev := (hf.eventually (by simp)).and hDbound.bound
  obtain ⟨δ,hδ,hδball⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨C,hC,δ,hδ,?_⟩
  intro y hy
  let r := ‖y-x‖
  let g : E → ℝ := fun z => f z-f x-fderiv ℝ f x (z-x)
  have hsmall (z : E) (hz : z ∈ closedBall x r) : z ∈ ball x δ := by
    rw [mem_ball,dist_eq_norm]
    exact (show ‖z-x‖ ≤ r by simpa only [mem_closedBall,dist_eq_norm] using hz).trans_lt hy
  have hgD (z : E) (hz : z ∈ closedBall x r) :
      HasFDerivAt g (fderiv ℝ f z-fderiv ℝ f x) z := by
    have hc := ((hδball (hsmall z hz)).1.differentiableAt (by norm_num)).hasFDerivAt
    have hlin := (fderiv ℝ f x).hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const x)
    simpa only [g,Pi.sub_def,Function.comp_def,id_eq,ContinuousLinearMap.comp_id] using (hc.sub_const (f x)).sub hlin
  have hb (z : E) (hz : z ∈ closedBall x r) : ‖fderiv ℝ g z‖ ≤ C*r := by
    rw [(hgD z hz).fderiv]
    exact (hδball (hsmall z hz)).2.trans (mul_le_mul_of_nonneg_left
      (show ‖z-x‖ ≤ r by simpa only [mem_closedBall,dist_eq_norm] using hz) hC.le)
  have hh := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z hz => (hgD z hz).differentiableAt) hb (convex_closedBall x r)
    (show x ∈ closedBall x r by simp [r])
    (show y ∈ closedBall x r by simp [r,dist_eq_norm])
  simpa only [g,sub_self,map_zero,sub_zero,Real.norm_eq_abs,r,pow_two,mul_assoc] using hh

end PowerConvexity
