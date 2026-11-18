import PowerConvexity.Analysis.ActualUniformClosureMixedModulusFour
import PowerConvexity.Calculus.ClosureJetContDiff

/-! # A true affine boundary remainder identifies the actual closure derivative -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open Set Filter Metric Asymptotics
open scoped Topology
namespace PowerConvexity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem actual_affine_remainder_hasFDerivWithinAt_four
    {U : Set E} {u : E → ℝ} {c : E} {L : E →L[ℝ] ℝ} {R C alpha : ℝ}
    (hR : 0 < R) (hC : 0 ≤ C) (ha : 0 < alpha) (hu0 : u c=0)
    (herr : ∀ x ∈ U, ‖x-c‖ < R → |u x-L (x-c)| ≤ C*‖x-c‖*‖x-c‖^alpha) :
    HasFDerivWithinAt u L U c := by
  have hp : Tendsto (fun x : E => C*‖x-c‖^alpha) (𝓝 c) (𝓝 0) := by
    have hn : Tendsto (fun x : E => ‖x-c‖) (𝓝 c) (𝓝 0) := by
      have hnorm : Continuous (fun x : E => ‖x-c‖) := by fun_prop
      simpa only [sub_self,norm_zero] using hnorm.tendsto c
    simpa only [mul_zero] using (hn.rpow_const_nhds_zero ha).const_mul C
  apply HasFDerivWithinAt.of_isLittleO
  apply Asymptotics.IsLittleO.of_bound
  intro eps heps
  have hs : ∀ᶠ x : E in 𝓝 c, C*‖x-c‖^alpha < eps := hp.eventually (gt_mem_nhds heps)
  have hb : ∀ᶠ x : E in 𝓝 c, x ∈ ball c R := Metric.ball_mem_nhds c hR
  filter_upwards [self_mem_nhdsWithin,hs.filter_mono nhdsWithin_le_nhds,
    hb.filter_mono nhdsWithin_le_nhds] with x hx hsx hxR
  have hh := herr x hx (by simpa only [mem_ball,dist_eq_norm] using hxR)
  have hh' : |u x-L (x-c)| ≤ eps*‖x-c‖ :=
    hh.trans ((show C*‖x-c‖*‖x-c‖^alpha=(C*‖x-c‖^alpha)*‖x-c‖ by ring).le.trans
      (mul_le_mul_of_nonneg_right hsx.le (norm_nonneg _)))
  simpa only [hu0,sub_zero,Real.norm_eq_abs] using hh'

theorem actual_affine_remainder_identifies_closure_derivative_four
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) {u : E → ℝ} {c : E}
    (hc : c ∈ closure U) {L J : E →L[ℝ] ℝ} {R C alpha : ℝ}
    (hR : 0 < R) (hC : 0 ≤ C) (ha : 0 < alpha) (hu0 : u c=0)
    (hJ : HasFDerivWithinAt u J (closure U) c)
    (herr : ∀ x ∈ U, ‖x-c‖ < R → |u x-L (x-c)| ≤ C*‖x-c‖*‖x-c‖^alpha) :
    J=L := by
  have hne : U.Nonempty := closure_nonempty_iff.mp ⟨c,hc⟩
  have hInt : (interior U).Nonempty := by simpa only [hU.interior_eq] using hne
  have hud := uniqueDiffWithinAt_convex hconv hInt hc
  exact hud.eq (hJ.mono subset_closure)
    (actual_affine_remainder_hasFDerivWithinAt_four hR hC ha hu0 herr)

end PowerConvexity
