import PowerConvexity.Calculus.LocalQuadraticRemainder

/-! # Uniform first-jet and quadratic remainder bounds on a convex ball -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Metric Filter
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fderiv_lipschitz_on_closedBall_of_Hessian_bound
    {f : E → ℝ} {x : E} {R C : ℝ}
    (hf : ∀ y ∈ closedBall x R, ContDiffAt ℝ 2 f y)
    (hH : ∀ y ∈ closedBall x R, ‖realHessian f y‖ ≤ C)
    {y z : E} (hy : y ∈ closedBall x R) (hz : z ∈ closedBall x R) :
    ‖fderiv ℝ f z-fderiv ℝ f y‖ ≤ C*‖z-y‖ := by
  exact Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun w hw => ((hf w hw).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
    hH (convex_closedBall x R) hy hz

theorem quadratic_remainder_on_closedBall_of_Hessian_bound
    {f : E → ℝ} {x : E} {R C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ y ∈ closedBall x R, ContDiffAt ℝ 2 f y)
    (hH : ∀ y ∈ closedBall x R, ‖realHessian f y‖ ≤ C)
    {y z : E} (hy : y ∈ closedBall x R) (hz : z ∈ closedBall x R) :
    |f z-f y-fderiv ℝ f y (z-y)| ≤ C*‖z-y‖^2 := by
  let S := closedBall x R ∩ closedBall y ‖z-y‖
  let g : E → ℝ := fun w => f w-f y-fderiv ℝ f y (w-y)
  have hgd (w : E) (hw : w ∈ S) :
      HasFDerivAt g (fderiv ℝ f w-fderiv ℝ f y) w := by
    have hlin := (fderiv ℝ f y).hasFDerivAt.comp w ((hasFDerivAt_id w).sub_const y)
    simpa only [g,Pi.sub_def,Function.comp_def,id_eq,ContinuousLinearMap.comp_id] using
      (((hf w hw.1).differentiableAt (by norm_num)).hasFDerivAt.sub_const (f y)).sub hlin
  have hb (w : E) (hw : w ∈ S) : ‖fderiv ℝ g w‖ ≤ C*‖z-y‖ := by
    rw [(hgd w hw).fderiv]
    exact (fderiv_lipschitz_on_closedBall_of_Hessian_bound hf hH hy hw.1).trans
      (mul_le_mul_of_nonneg_left (by simpa only [mem_closedBall,dist_eq_norm] using hw.2) hC)
  have hh := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun w hw => (hgd w hw).differentiableAt) hb
    ((convex_closedBall x R).inter (convex_closedBall y ‖z-y‖))
    (show y ∈ S from ⟨hy,by simp⟩) (show z ∈ S from ⟨hz,by simp [dist_eq_norm]⟩)
  simpa only [g,sub_self,map_zero,sub_zero,Real.norm_eq_abs,pow_two,mul_assoc] using hh

theorem exists_local_uniform_Hessian_bound {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) :
    ∃ C > 0, ∃ R > 0,
      (∀ y ∈ closedBall x R, ContDiffAt ℝ 2 f y) ∧
      ∀ y ∈ closedBall x R, ‖realHessian f y‖ ≤ C := by
  letI : TopologicalSpace (E →L[ℝ] E →L[ℝ] ℝ) :=
    (inferInstance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace
  have hH : ContinuousAt (realHessian f) x :=
    (((hf.fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num))).continuousAt
  let C := ‖realHessian f x‖+1
  have hC : 0 < C := by dsimp only [C]; positivity
  have hN : ContinuousAt (fun y => ‖realHessian f y‖) x := by
    exact ContinuousAt.norm (E := E →L[ℝ] E →L[ℝ] ℝ) hH
  have hbound : ∀ᶠ y in 𝓝 x, ‖realHessian f y‖ < C :=
    hN.tendsto.eventually (gt_mem_nhds (by dsimp only [C]; linarith))
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp ((hf.eventually (by simp)).and hbound)
  refine ⟨C,hC,δ/2,by positivity,?_,?_⟩
  · intro y hy
    exact (hball ((closedBall_subset_ball (by linarith : δ/2 < δ)) hy)).1
  · intro y hy
    exact (hball ((closedBall_subset_ball (by linarith : δ/2 < δ)) hy)).2.le

end PowerConvexity
