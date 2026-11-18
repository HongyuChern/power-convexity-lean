import PowerConvexity.Calculus.GaussianBarrier

/-! # A nonzero barrier derivative excludes an interior zero contact -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff Topology

namespace PowerConvexity
open CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E]

section Linear
variable [NormedSpace ℝ E]

theorem no_zero_contact_of_nonzero_barrier_derivative {w v : E → ℝ} {x : E}
    (hw : DifferentiableAt ℝ w x) (hv : DifferentiableAt ℝ v x)
    (hw0 : w x = 0) (hv0 : v x = 0)
    (hwn : ∀ᶠ y in 𝓝 x, 0 ≤ w y) {ε : ℝ} (hε : 0 < ε)
    (hcomp : ∀ᶠ y in 𝓝 x, ε * v y ≤ w y)
    (hDv : fderiv ℝ v x ≠ 0) : False := by
  have hmw : IsLocalMin w x := by
    filter_upwards [hwn] with y hy
    simpa [hw0] using hy
  have hmf : IsLocalMin (fun y => w y - ε * v y) x := by
    filter_upwards [hcomp] with y hy
    simpa [hw0, hv0] using sub_nonneg.mpr hy
  have hD := fderiv_eq_of_isLocalMin_sub hw ((differentiableAt_const ε).mul hv) hmf
  change fderiv ℝ w x = fderiv ℝ (fun y => ε * v y) x at hD
  rw [hmw.fderiv_eq_zero, fderiv_const_mul hv] at hD
  exact hDv ((smul_eq_zero.mp hD.symm).resolve_left (ne_of_gt hε))

end Linear

section Inner
variable [InnerProductSpace ℝ E]

theorem annularBarrier_nonpos_outside {k R : ℝ} (hk : 0 ≤ k) (hR : 0 ≤ R)
    (c y : E) (hy : R ≤ ‖y-c‖) : annularBarrier k R c y ≤ 0 := by
  have hsq : R^2 ≤ ‖y-c‖^2 := (sq_le_sq₀ hR (norm_nonneg _)).mpr hy
  have hh := mul_le_mul_of_nonpos_left hsq (neg_nonpos.mpr hk)
  exact sub_nonpos.mpr (Real.exp_le_exp.mpr hh)

theorem fderiv_annularBarrier_ne_zero {k R : ℝ} (hk : 0 < k) (hR : 0 < R)
    (c x : E) (hx : ‖x-c‖ = R) : fderiv ℝ (annularBarrier k R c) x ≠ 0 := by
  apply norm_pos_iff.mp
  rw [norm_fderiv_annularBarrier hk.le, hx]
  have hG : 0 < radialGaussian k c x := Real.exp_pos _
  positivity

/-- Comparison inside the annulus extends across its outer sphere because
the barrier is nonpositive outside and w is nonnegative near the contact. -/
theorem annular_zero_contact_impossible {w : E → ℝ} {x c : E} {k R ε : ℝ}
    (hk : 0 < k) (hR : 0 < R) (hε : 0 < ε)
    (hw : DifferentiableAt ℝ w x) (hw0 : w x = 0)
    (hwn : ∀ᶠ y in 𝓝 x, 0 ≤ w y) (hx : ‖x-c‖ = R)
    (hcomp : ∀ y, R/2 ≤ ‖y-c‖ → ‖y-c‖ ≤ R → ε * annularBarrier k R c y ≤ w y) :
    False := by
  have hr : ∀ᶠ y in 𝓝 x, R/2 < ‖y-c‖ := by
    apply continuousAt_const.eventually_lt ((continuousAt_id.sub continuousAt_const).norm)
    change R/2 < ‖x-c‖
    rw [hx]
    linarith
  have hc : ∀ᶠ y in 𝓝 x, ε * annularBarrier k R c y ≤ w y := by
    filter_upwards [hr, hwn] with y hyr hyw
    by_cases hy : ‖y-c‖ ≤ R
    · exact hcomp y hyr.le hy
    · have hv := annularBarrier_nonpos_outside hk.le hR.le c y (le_of_lt (lt_of_not_ge hy))
      exact (mul_nonpos_of_nonneg_of_nonpos hε.le hv).trans hyw
  exact no_zero_contact_of_nonzero_barrier_derivative hw
    ((annularBarrier_contDiff k R c (n := 2)).differentiable (by norm_num)).differentiableAt
    hw0 (annularBarrier_zero_on_sphere k R c x hx) hwn hε hc
    (fderiv_annularBarrier_ne_zero hk hR c x hx)

end Inner
end PowerConvexity
