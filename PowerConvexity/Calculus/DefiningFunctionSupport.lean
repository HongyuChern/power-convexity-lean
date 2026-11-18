import PowerConvexity.Calculus.LocalQuadraticRemainder
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.InnerProductSpace.Dual

/-! # The inward sign of a regular defining-function normal on a convex domain -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open Set Metric Filter
open scoped ContDiff Topology
namespace PowerConvexity
variable {E : Type*} [NormedAddCommGroup E]
section Normed
variable [NormedSpace ℝ E]

theorem definingFunction_support_nonpos
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U)
    {x : E} (hx : x ∈ closure U) {f : E → ℝ}
    (hf : DifferentiableAt ℝ f x) (hfx : f x = 0)
    (hdef : ∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0) :
    ∀ y ∈ U, fderiv ℝ f x (y-x) ≤ 0 := by
  intro y hy
  let d := y-x
  let p : ℝ → E := fun t => x+t • d
  have hp : HasDerivAt p d 0 := by
    simpa only [p,id_eq,one_smul] using ((hasDerivAt_id (0:ℝ)).smul_const d).const_add x
  have hp0 : p 0 = x := by simp [p]
  have hfp : HasDerivAt (fun t => f (p t)) (fderiv ℝ f x d) 0 := by
    exact (hf.hasFDerivAt.comp_hasDerivAt_of_eq 0 hp hp0.symm)
  have hnear : ∀ᶠ t in 𝓝 (0:ℝ), p t ∈ U ↔ f (p t) < 0 :=
    (hp.continuousAt.tendsto.mono_right (by rw [hp0])).eventually hdef
  have hslope : ∀ᶠ t in 𝓝[>] (0:ℝ),
      t⁻¹ • ((fun t => f (p t)) (0+t)-(fun t => f (p t)) 0) ≤ 0 := by
    filter_upwards [self_mem_nhdsWithin,
      hnear.filter_mono nhdsWithin_le_nhds,
      (gt_mem_nhds (by norm_num : (0:ℝ) < 1)).filter_mono nhdsWithin_le_nhds] with t ht hnt ht1
    have hpt : p t ∈ U := by
      rw [← hU.interior_eq]
      exact hconv.add_smul_sub_mem_interior' hx (by rwa [hU.interior_eq]) ⟨ht,ht1.le⟩
    have hfpt := (hnt.mp hpt).le
    simpa only [zero_add,hp0,hfx,sub_zero,smul_eq_mul] using
      mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr ht.le) hfpt
  exact le_of_tendsto hfp.tendsto_slope_zero_right hslope

end Normed
variable [InnerProductSpace ℝ E]

theorem strict_support_of_nonzero_normal
    {U : Set E} (hU : IsOpen U) {x N : E} (hN : N ≠ 0)
    (hsupport : ∀ y ∈ U, inner ℝ N (y-x) ≤ 0) :
    ∀ y ∈ U, inner ℝ N (y-x) < 0 := by
  intro y hy
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hy)
  let ε := δ/(2*(‖N‖+1))
  have hε : 0 < ε := div_pos hδ (by positivity)
  have he : ε*(2*(‖N‖+1)) = δ := by dsimp [ε]; field_simp
  have hnear : y+ε • N ∈ ball y δ := by
    rw [mem_ball,dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hε]
    nlinarith [norm_nonneg N]
  have hh := hsupport (y+ε • N) (hball hnear)
  rw [show y+ε • N-x = (y-x)+ε • N by abel,inner_add_right,
    real_inner_smul_right,real_inner_self_eq_norm_sq] at hh
  have hp := mul_pos hε (sq_pos_of_pos (norm_pos_iff.mpr hN))
  linarith

end PowerConvexity
