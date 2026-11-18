import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Operator.Basic

/-! # A quantitative derivative stability estimate from values and oscillations -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
open Set Metric
namespace PowerConvexity
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem fderiv_distance_le_of_value_and_derivative_oscillation
    {f g : E → F} {x : E} {r ε η : ℝ} (hr : 0 < r) (hε : 0 ≤ ε) (hη : 0 ≤ η)
    (hf : ∀ z ∈ closedBall x r, DifferentiableAt ℝ f z)
    (hg : ∀ z ∈ closedBall x r, DifferentiableAt ℝ g z)
    (hDf : ∀ z ∈ closedBall x r, ‖fderiv ℝ f z-fderiv ℝ f x‖ ≤ η)
    (hDg : ∀ z ∈ closedBall x r, ‖fderiv ℝ g z-fderiv ℝ g x‖ ≤ η)
    (hval : ∀ z ∈ closedBall x r, ‖f z-g z‖ ≤ ε) :
    ‖fderiv ℝ f x-fderiv ℝ g x‖ ≤ 2*η+2*ε/r := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro v hv
  let z := x+r • v
  have hstep : ‖z-x‖ = r := by
    simp only [z,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hr,hv,mul_one]
  have hx : x ∈ closedBall x r := mem_closedBall_self hr.le
  have hz : z ∈ closedBall x r := by rw [mem_closedBall,dist_eq_norm,hstep]
  have hrf := (convex_closedBall x r).norm_image_sub_le_of_norm_fderiv_le' hf hDf hx hz
  have hrg := (convex_closedBall x r).norm_image_sub_le_of_norm_fderiv_le' hg hDg hx hz
  rw [hstep] at hrf hrg
  let L := fderiv ℝ f x-fderiv ℝ g x
  have he : L (z-x) =
      (f z-g z)-(f x-g x)-(f z-f x-fderiv ℝ f x (z-x))+
        (g z-g x-fderiv ℝ g x (z-x)) := by
    simp only [L,ContinuousLinearMap.sub_apply]
    abel
  have hb : ‖L (z-x)‖ ≤ 2*ε+2*η*r := by
    rw [he]
    have h1 := norm_add_le ((f z-g z)-(f x-g x)-(f z-f x-fderiv ℝ f x (z-x)))
      (g z-g x-fderiv ℝ g x (z-x))
    have h2 := norm_sub_le ((f z-g z)-(f x-g x)) (f z-f x-fderiv ℝ f x (z-x))
    have h3 := norm_sub_le (f z-g z) (f x-g x)
    linarith [hval z hz,hval x hx]
  have heval : ‖L (z-x)‖ = r*‖L v‖ := by
    simp only [z,add_sub_cancel_left,map_smul,norm_smul,Real.norm_eq_abs,abs_of_pos hr]
  rw [heval] at hb
  have hq : ‖L v‖ ≤ (2*ε+2*η*r)/r :=
    (le_div_iff₀ hr).mpr (by simpa only [mul_comm] using hb)
  have heq : (2*ε+2*η*r)/r = 2*η+2*ε/r := by field_simp [hr.ne'] <;> ring
  rw [heq] at hq
  exact hq

end PowerConvexity
