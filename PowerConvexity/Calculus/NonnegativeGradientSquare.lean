import PowerConvexity.Calculus.UniformQuadraticRemainder
import Mathlib.Analysis.InnerProductSpace.Dual

/-! # A local squared-gradient bound for a nonnegative C2 function

This estimate controls quadratic first-derivative errors at a zero contact.
It does not replace a strong minimum principle for linear gradient errors.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open Set Metric Filter
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem gradient_sq_le_on_ball_of_nonnegative_Hessian_bound
    {f : E → ℝ} {x : E} {R C : ℝ} (hR : 0 < R) (hC : 0 < C)
    (hf : ∀ y ∈ closedBall x R, ContDiffAt ℝ 2 f y)
    (hH : ∀ y ∈ closedBall x R, ‖realHessian f y‖ ≤ C)
    (hn : ∀ y ∈ closedBall x R, 0 ≤ f y) (hx0 : f x = 0)
    {y : E} (hy : y ∈ ball x (R/2)) : ‖fderiv ℝ f y‖^2 ≤ 4*C*f y := by
  have hxc : x ∈ closedBall x R := mem_closedBall_self hR.le
  have hyc : y ∈ closedBall x R := ball_subset_closedBall
    ((ball_subset_ball (by linarith : R/2 ≤ R)) hy)
  have hm : IsLocalMin f x := by
    filter_upwards [ball_mem_nhds x hR] with z hz
    simpa only [hx0] using hn z (ball_subset_closedBall hz)
  have hDx : fderiv ℝ f x = 0 := hm.fderiv_eq_zero
  have hDy : ‖fderiv ℝ f y‖ ≤ C*‖y-x‖ := by
    simpa only [hDx,sub_zero] using fderiv_lipschitz_on_closedBall_of_Hessian_bound hf hH hxc hyc
  let v := (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f y)
  have hv : ‖v‖ = ‖fderiv ℝ f y‖ := (InnerProductSpace.toDual ℝ E).symm.norm_map _
  have hDv : fderiv ℝ f y v = ‖v‖^2 := by
    rw [← InnerProductSpace.toDual_symm_apply,real_inner_self_eq_norm_sq]
  let t := (2*C)⁻¹
  have ht : 0 < t := inv_pos.mpr (by positivity)
  let z := y+(-t) • v
  have hstep : ‖z-y‖ = t*‖v‖ := by
    simp only [z,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_neg,abs_of_pos ht]
  have hCn : C ≠ 0 := hC.ne'
  have htC : t*C = 1/2 := by dsimp only [t]; field_simp [hCn] <;> ring
  have hdist : ‖y-x‖ < R/2 := by simpa only [mem_ball,dist_eq_norm] using hy
  have hz : z ∈ closedBall x R := by
    rw [mem_closedBall,dist_eq_norm]
    have he : z-x = (z-y)+(y-x) := by abel
    rw [he]
    have hb := mul_le_mul_of_nonneg_left hDy ht.le
    rw [← hv] at hb
    have hs : ‖z-y‖ ≤ ‖y-x‖/2 := by
      rw [hstep]
      calc
        t*‖v‖ ≤ t*(C*‖y-x‖) := hb
        _ = ‖y-x‖/2 := by rw [← mul_assoc,htC]; ring
    exact (norm_add_le _ _).trans (by linarith)
  have hDz : fderiv ℝ f y (z-y) = -t*‖v‖^2 := by
    simp only [z,add_sub_cancel_left,map_smul,smul_eq_mul,hDv]
  have he := (abs_le.mp (quadratic_remainder_on_closedBall_of_Hessian_bound hC.le hf hH hyc hz)).2
  rw [hDz,hstep] at he
  have hcoef : t-C*t^2 = 1/(4*C) := by dsimp only [t]; field_simp [hCn] <;> ring
  have hmain : (t-C*t^2)*‖v‖^2 ≤ f y := by nlinarith [hn z hz]
  rw [hcoef,hv] at hmain
  have hh := mul_le_mul_of_nonneg_left hmain (by positivity : 0 ≤ 4*C)
  have hcancel : (4*C)*(1/(4*C)*‖fderiv ℝ f y‖^2) = ‖fderiv ℝ f y‖^2 := by
    field_simp [hCn]
  rw [hcancel] at hh
  nlinarith only [hh]

theorem exists_local_gradient_sq_bound_at_nonnegative_zero
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x)
    (hn : ∀ᶠ y in 𝓝 x, 0 ≤ f y) (hx0 : f x = 0) :
    ∃ C > 0, ∀ᶠ y in 𝓝 x, ‖fderiv ℝ f y‖^2 ≤ C*f y := by
  obtain ⟨C,hC,R,hR,hfR,hHR⟩ := exists_local_uniform_Hessian_bound hf
  obtain ⟨δ,hδ,hδn⟩ := Metric.mem_nhds_iff.mp hn
  let r := min R (δ/2)
  have hr : 0 < r := lt_min hR (by positivity)
  have hsub : closedBall x r ⊆ closedBall x R := closedBall_subset_closedBall (min_le_left _ _)
  have hsubδ : closedBall x r ⊆ ball x δ :=
    closedBall_subset_ball ((min_le_right _ _).trans_lt (by linarith))
  refine ⟨4*C,by positivity,?_⟩
  filter_upwards [ball_mem_nhds x (by positivity : 0 < r/2)] with y hy
  exact gradient_sq_le_on_ball_of_nonnegative_Hessian_bound hr hC
    (fun z hz => hfR z (hsub hz)) (fun z hz => hHR z (hsub hz))
    (fun z hz => hδn (hsubδ hz)) hx0 hy

theorem exists_local_gradient_sq_bound_of_two_sided_majorant
    {φ g : E → ℝ} {x : E} (hφ : ContDiffAt ℝ 2 φ x) (hg : ContDiffAt ℝ 2 g x)
    (hpos : ∀ᶠ y in 𝓝 x, 0 ≤ φ y+g y ∧ 0 ≤ φ y-g y)
    (hφ0 : φ x = 0) (hg0 : g x = 0) :
    ∃ C > 0, ∀ᶠ y in 𝓝 x, ‖fderiv ℝ g y‖^2 ≤ C*φ y := by
  obtain ⟨Cp,hCp,hp⟩ := exists_local_gradient_sq_bound_at_nonnegative_zero
    (hφ.add hg) (hpos.mono fun _ hy => hy.1) (by simp [hφ0,hg0])
  obtain ⟨Cm,hCm,hm⟩ := exists_local_gradient_sq_bound_at_nonnegative_zero
    (hφ.sub hg) (hpos.mono fun _ hy => hy.2) (by simp [hφ0,hg0])
  refine ⟨Cp+Cm,by positivity,?_⟩
  filter_upwards [hp,hm,hpos,hφ.eventually (by simp),hg.eventually (by simp)] with y hyp hym hyn hyφ hyg
  have hφD := hyφ.differentiableAt (by norm_num)
  have hgD := hyg.differentiableAt (by norm_num)
  have he : fderiv ℝ (fun z => φ z+g z) y-fderiv ℝ (fun z => φ z-g z) y =
      (2:ℝ) • fderiv ℝ g y := by
    rw [fderiv_fun_add hφD hgD,fderiv_fun_sub hφD hgD]
    module
  have hnorm := norm_sub_le (fderiv ℝ (fun z => φ z+g z) y) (fderiv ℝ (fun z => φ z-g z) y)
  rw [he,norm_smul] at hnorm
  norm_num only [Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ) < 2)] at hnorm
  have hsquare := pow_le_pow_left₀ (by positivity : 0 ≤ 2*‖fderiv ℝ g y‖) hnorm 2
  have hp' := hyp.trans (mul_le_mul_of_nonneg_right (by linarith : Cp ≤ Cp+Cm) hyn.1)
  have hm' := hym.trans (mul_le_mul_of_nonneg_right (by linarith : Cm ≤ Cp+Cm) hyn.2)
  nlinarith [sq_nonneg (‖fderiv ℝ (fun z => φ z+g z) y‖-‖fderiv ℝ (fun z => φ z-g z) y‖)]

end PowerConvexity
