import PowerConvexity.Calculus.ConvexHessian
import PowerConvexity.Calculus.NonnegativeGradientSquare

/-! # Quantitative first-derivative stability from convexity and value control

Only the comparison function needs a C2 Hessian bound. No derivative bound on
the varying convex function is assumed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open Set Metric
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus

section FirstDerivative
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem convexOn_fderiv_sub_le {U : Set E} {f : E → ℝ}
    (hf : ConvexOn ℝ U f) {x z : E} (hx : x ∈ U) (hz : z ∈ U)
    (hD : DifferentiableAt ℝ f x) : fderiv ℝ f x (z-x) ≤ f z-f x := by
  let γ : ℝ →ᵃ[ℝ] E := AffineMap.lineMap x z
  have hconv := hf.comp_affineMap γ
  have h0 : (0:ℝ) ∈ γ ⁻¹' U := by simpa [γ] using hx
  have h1 : (1:ℝ) ∈ γ ⁻¹' U := by simpa [γ] using hz
  have hγ : HasDerivAt (γ : ℝ → E) (z-x) 0 := AffineMap.hasDerivAt_lineMap
  have hdx : DifferentiableAt ℝ f (γ 0) := by simpa [γ] using hD
  have hd := hdx.hasFDerivAt.comp_hasDerivAt 0 hγ
  have hh := hconv.le_slope_of_hasDerivAt h0 h1 (by norm_num) hd
  simpa only [slope_def_field,Function.comp_apply,γ,AffineMap.lineMap_apply_zero,
    AffineMap.lineMap_apply_one,sub_zero,div_one] using hh

end FirstDerivative

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem convex_fderiv_distance_le_of_value_bound
    {f g : E → ℝ} {x y : E} {R C ε t : ℝ}
    (hR : 0 < R) (hC : 0 ≤ C) (hε : 0 ≤ ε) (ht : 0 < t) (htR : t ≤ R/2)
    (hf : ConvexOn ℝ (closedBall x R) f) (hfy : DifferentiableAt ℝ f y)
    (hg : ∀ z ∈ closedBall x R, ContDiffAt ℝ 2 g z)
    (hH : ∀ z ∈ closedBall x R, ‖realHessian g z‖ ≤ C)
    (hval : ∀ z ∈ closedBall x R, |f z-g z| ≤ ε)
    (hy : y ∈ ball x (R/2)) :
    ‖fderiv ℝ f y-fderiv ℝ g y‖ ≤ C*t+2*ε/t := by
  let D := fderiv ℝ f y-fderiv ℝ g y
  have hyc : y ∈ closedBall x R := ball_subset_closedBall
    ((ball_subset_ball (by linarith : R/2 ≤ R)) hy)
  by_cases hD : D = 0
  · change ‖D‖ ≤ _
    rw [hD,norm_zero]
    positivity
  have hDn : 0 < ‖D‖ := norm_pos_iff.mpr hD
  let w := (InnerProductSpace.toDual ℝ E).symm D
  have hw : ‖w‖ = ‖D‖ := (InnerProductSpace.toDual ℝ E).symm.norm_map _
  have hDw : D w = ‖w‖^2 := by
    rw [← InnerProductSpace.toDual_symm_apply,real_inner_self_eq_norm_sq]
  let v := ‖D‖⁻¹ • w
  have hv : ‖v‖ = 1 := by simp [v,norm_smul,hw,hDn.ne']
  have hDv : D v = ‖D‖ := by
    simp only [v,map_smul,smul_eq_mul,hDw,hw]
    field_simp [hDn.ne']
  let z := y+t • v
  have hstep : ‖z-y‖ = t := by
    simp only [z,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos ht,hv,mul_one]
  have hyR : ‖y-x‖ < R/2 := by simpa only [mem_ball,dist_eq_norm] using hy
  have hzc : z ∈ closedBall x R := by
    rw [mem_closedBall,dist_eq_norm]
    have he : z-x = (z-y)+(y-x) := by abel
    rw [he]
    exact (norm_add_le _ _).trans (by rw [hstep]; linarith)
  have hff := convexOn_fderiv_sub_le hf hyc hzc hfy
  have hgg := (abs_le.mp (quadratic_remainder_on_closedBall_of_Hessian_bound hC hg hH hyc hzc)).2
  have hyval := abs_le.mp (hval y hyc)
  have hzval := abs_le.mp (hval z hzc)
  have hDstep : fderiv ℝ f y (z-y)-fderiv ℝ g y (z-y) = t*‖D‖ := by
    change D (z-y) = _
    simp only [z,add_sub_cancel_left,map_smul,smul_eq_mul,hDv]
  rw [hstep] at hgg
  have hh : t*‖D‖ ≤ C*t^2+2*ε := by nlinarith only [hff,hgg,hyval.1,hzval.2,hDstep]
  change ‖D‖ ≤ _
  have hquot : ‖D‖ ≤ (C*t^2+2*ε)/t :=
    (le_div_iff₀ ht).mpr (by simpa only [mul_comm t ‖D‖] using hh)
  have he : (C*t^2+2*ε)/t = C*t+2*ε/t := by field_simp [ht.ne'] <;> ring
  rw [he] at hquot
  exact hquot

end PowerConvexity
