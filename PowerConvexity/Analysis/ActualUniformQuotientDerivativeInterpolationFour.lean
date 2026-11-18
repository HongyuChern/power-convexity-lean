import PowerConvexity.Analysis.ActualUniformQuotientMixedJetFour
import Mathlib.Analysis.Calculus.MeanValue

/-! # Actual derivative interpolation for the boundary quotient remainder

The value estimate is combined with an actual interior derivative modulus by
a real finite difference. No derivative estimate for general rough linear
coefficients is invoked.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem actual_firstTaylor_error_of_derivative_modulus_four
    {u : V → ℝ} {c : V} {r eta : ℝ} (hr : 0 < r)
    (hu : ∀ x ∈ closedBall c r, DifferentiableAt ℝ u x)
    (hmod : ∀ x ∈ closedBall c r, ‖fderiv ℝ u x-fderiv ℝ u c‖ ≤ eta) :
    ∀ x ∈ closedBall c r,
      |u x-u c-fderiv ℝ u c (x-c)| ≤ eta*‖x-c‖ := by
  let F : V → ℝ := fun x => u x-u c-fderiv ℝ u c (x-c)
  have hderiv (x : V) (hx : x ∈ closedBall c r) :
      HasFDerivAt F (fderiv ℝ u x-fderiv ℝ u c) x := by
    have haff : HasFDerivAt (fun y : V => fderiv ℝ u c (y-c)) (fderiv ℝ u c) x := by
      simpa only [map_sub] using
        ((fderiv ℝ u c).hasFDerivAt (x := x)).sub_const (fderiv ℝ u c c)
    exact ((hu x hx).hasFDerivAt.sub_const (u c)).sub haff
  have hF0 : F c=0 := by simp only [F,sub_self,map_zero]
  intro x hx
  have hh := (convex_closedBall c r).norm_image_sub_le_of_norm_fderiv_le
    (fun y hy => (hderiv y hy).differentiableAt)
    (fun y hy => by rw [(hderiv y hy).fderiv]; exact hmod y hy)
    (mem_closedBall_self hr.le) hx
  simpa only [hF0,sub_zero,Real.norm_eq_abs] using hh

theorem actual_derivative_bound_from_value_and_modulus_four
    {u : V → ℝ} {c : V} {r E eta : ℝ} (hr : 0 < r) (hE : 0 ≤ E) (heta : 0 ≤ eta)
    (hu : ∀ x ∈ closedBall c r, DifferentiableAt ℝ u x)
    (hvalue : ∀ x ∈ closedBall c r, |u x| ≤ E)
    (hmod : ∀ x ∈ closedBall c r, ‖fderiv ℝ u x-fderiv ℝ u c‖ ≤ eta) :
    ‖fderiv ℝ u c‖ ≤ 2*E/r+eta := by
  have hc : c ∈ closedBall c r := mem_closedBall_self hr.le
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro v hv
  let x := c+r • v
  have hnorm : ‖x-c‖=r := by
    simp only [x,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hr,hv,mul_one]
  have hx : x ∈ closedBall c r := by simpa only [mem_closedBall,dist_eq_norm,hnorm] using le_refl r
  have herror := actual_firstTaylor_error_of_derivative_modulus_four hr hu hmod x hx
  rw [hnorm] at herror
  have hid : r*fderiv ℝ u c v=
      u x-u c-(u x-u c-fderiv ℝ u c (x-c)) := by
    simp only [x,add_sub_cancel_left,map_smul,smul_eq_mul]
    ring
  have hb : r*|fderiv ℝ u c v| ≤ 2*E+eta*r := by
    calc
      _ = |r*fderiv ℝ u c v| := by rw [abs_mul,abs_of_pos hr]
      _ = |u x-u c-(u x-u c-fderiv ℝ u c (x-c))| := congrArg abs hid
      _ ≤ |u x-u c|+|u x-u c-fderiv ℝ u c (x-c)| := abs_sub _ _
      _ ≤ (|u x|+|u c|)+|u x-u c-fderiv ℝ u c (x-c)| :=
        add_le_add (abs_sub _ _) le_rfl
      _ ≤ (E+E)+eta*r := add_le_add (add_le_add (hvalue x hx) (hvalue c hc)) herror
      _ = _ := by ring
  change |fderiv ℝ u c v| ≤ 2*E/r+eta
  have hcancel : (2*E/r)*r=2*E := by field_simp
  nlinarith

theorem actual_derivative_from_holder_affine_remainder_four
    {u : V → ℝ} {c : V} {L : V →L[ℝ] ℝ} {k E H beta R h : ℝ}
    (hE : 0 ≤ E) (hH : 0 ≤ H) (hbeta : 0 ≤ beta) (hh : 0 < h) (hhR : h < R)
    (hu : ∀ x ∈ ball c R, DifferentiableAt ℝ u x)
    (hvalue : ∀ x ∈ ball c R, |u x-(k+L (x-c))| ≤ E)
    (hmod : ∀ x ∈ ball c R,
      ‖fderiv ℝ u x-fderiv ℝ u c‖ ≤ H*(‖x-c‖/R)^beta) :
    ‖fderiv ℝ u c-L‖ ≤ 2*E/h+H*(h/R)^beta := by
  have hR : 0 < R := hh.trans hhR
  let w : V → ℝ := fun x => u x-(k+L (x-c))
  have hsub : closedBall c h ⊆ ball c R := closedBall_subset_ball hhR
  have hderiv (x : V) (hx : x ∈ closedBall c h) :
      HasFDerivAt w (fderiv ℝ u x-L) x := by
    have haff : HasFDerivAt (fun y : V => k+L (y-c)) L x := by
      simpa only [ContinuousLinearMap.comp_id,Function.comp_apply,id_eq] using
        ((L.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const c)).const_add k)
    exact (hu x (hsub hx)).hasFDerivAt.sub haff
  have hc : c ∈ closedBall c h := mem_closedBall_self hh.le
  have hwm : ∀ x ∈ closedBall c h,
      ‖fderiv ℝ w x-fderiv ℝ w c‖ ≤ H*(h/R)^beta := by
    intro x hx
    rw [(hderiv x hx).fderiv,(hderiv c hc).fderiv,sub_sub_sub_cancel_right]
    apply (hmod x (hsub hx)).trans
    apply mul_le_mul_of_nonneg_left _ hH
    apply Real.rpow_le_rpow (by positivity) _ hbeta
    exact div_le_div_of_nonneg_right
      (by simpa only [mem_closedBall,dist_eq_norm] using hx) hR.le
  have he := actual_derivative_bound_from_value_and_modulus_four hh hE (by positivity)
    (fun x hx => (hderiv x hx).differentiableAt)
    (fun x hx => hvalue x (hsub hx)) hwm
  rwa [(hderiv c hc).fderiv] at he

end PowerConvexity
