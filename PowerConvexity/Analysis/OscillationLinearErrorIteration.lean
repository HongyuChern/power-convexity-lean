import CHS.Analysis.GeometricOscillationDecay

/-! # Scalar oscillation iteration retaining a linear radius error.
The correction is explicit and positive. No limiting regularity statement
is inferred until an actual Hessian oscillation satisfies this recurrence.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace PowerConvexity
open CHS.Analysis

theorem eighth_contraction_after_linear_correction
    {F : ℝ → ℝ} {theta K r : ℝ} (htheta : (1/8 : ℝ) < theta)
    (hstep : F (r/8) ≤ theta*F r+K*r) :
    F (r/8)+(K/(theta-1/8))*(r/8) ≤
      theta*(F r+(K/(theta-1/8))*r) := by
  have hden : theta-1/8 ≠ 0 := (sub_pos.mpr htheta).ne'
  have he : (K/(theta-1/8))*(theta-1/8) = K := div_mul_cancel₀ _ hden
  nlinarith only [hstep,congrArg (fun a : ℝ => a*r) he]

theorem eighth_radius_linear_error_iterate
    {F : ℝ → ℝ} {theta K R : ℝ} (htheta : (1/8 : ℝ) < theta)
    (hK : 0 ≤ K) (hR : 0 < R)
    (hstep : ∀ r : ℝ, 0 < r → r ≤ R → F (r/8) ≤ theta*F r+K*r) :
    ∀ k : ℕ, F (R*(1/8 : ℝ)^k) ≤
      theta^k*(F R+(K/(theta-1/8))*R) := by
  let G : ℝ → ℝ := fun r => F r+(K/(theta-1/8))*r
  have htheta0 : 0 ≤ theta := by linarith
  have hGstep : ∀ r : ℝ, 0 < r → r ≤ R → G (r/8) ≤ theta*G r := by
    intro r hr hrR
    exact eighth_contraction_after_linear_correction htheta (hstep r hr hrR)
  have hiter := eighth_radius_contraction_iterate htheta0 hR hGstep
  intro k
  have hcor : 0 ≤ (K/(theta-1/8))*(R*(1/8 : ℝ)^k) :=
    mul_nonneg (div_nonneg hK (sub_pos.mpr htheta).le) (by positivity)
  exact (le_add_of_nonneg_right hcor).trans (hiter k)

theorem finiteOscillationFactor_one_eighth_lt
    {d : ℕ} [NeZero d] (hd : 2 < (d : ℝ)) (Lambda C : ℝ) (N : ℕ) :
    (1/8 : ℝ) < finiteOscillationFactor d hd Lambda C N := by
  have hD : 1 ≤ finiteOscillationConstant d hd Lambda C N := le_max_left _ _
  unfold finiteOscillationFactor
  apply (lt_div_iff₀ (by linarith : 0 < finiteOscillationConstant d hd Lambda C N+1)).mpr
  linarith

end PowerConvexity
