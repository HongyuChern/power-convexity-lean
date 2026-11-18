import PowerConvexity.Analysis.ContinuousEllipticity
import Mathlib.Analysis.InnerProductSpace.Dual

/-! # Elliptic contraction of actual gradient square forms -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
namespace PowerConvexity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def dualSquareForm (D : E →L[ℝ] ℝ) : E →L[ℝ] E →L[ℝ] ℝ := D.smulRight D

theorem dualSquareForm_apply (D : E →L[ℝ] ℝ) (v w : E) :
    dualSquareForm D v w = D v*D w := rfl

theorem bilinear_order_of_unit_sphere (H K : E →L[ℝ] E →L[ℝ] ℝ)
    (h : ∀ v : E, ‖v‖ = 1 → H v v ≤ K v v) : ∀ v : E, H v v ≤ K v v := by
  intro v
  by_cases hv : v = 0
  · simp [hv]
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hw : ‖‖v‖⁻¹ • v‖ = 1 := by simp [norm_smul,Real.norm_eq_abs,abs_of_pos hn,hn.ne']
  have hh := h (‖v‖⁻¹ • v) hw
  simp only [map_smul,smul_apply,smul_eq_mul] at hh
  have hi : 0 < ‖v‖⁻¹*‖v‖⁻¹ := mul_pos (inv_pos.mpr hn) (inv_pos.mpr hn)
  apply (mul_le_mul_iff_right₀ hi).mp
  simpa only [mul_assoc] using hh

variable [CompleteSpace E]

theorem dualSquareForm_eq_riesz (D : E →L[ℝ] ℝ) :
    dualSquareForm D = realRankOneForm ((InnerProductSpace.toDual ℝ E).symm D) := by
  ext v w
  simp only [dualSquareForm,realRankOneForm,ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply,smul_apply,smul_eq_mul,InnerProductSpace.toDual_symm_apply]

theorem dualSquareForm_contraction_lower
    (L : (E →L[ℝ] E →L[ℝ] ℝ) →ₗ[ℝ] ℝ) {ell : ℝ}
    (hlow : ∀ v : E, ell*‖v‖^2 ≤ L (realRankOneForm v)) (D : E →L[ℝ] ℝ) :
    ell*‖D‖^2 ≤ L (dualSquareForm D) := by
  rw [dualSquareForm_eq_riesz]
  simpa only [(InnerProductSpace.toDual ℝ E).symm.norm_map] using
    hlow ((InnerProductSpace.toDual ℝ E).symm D)

theorem hessian_contraction_of_three_square_bound
    (L : (E →L[ℝ] E →L[ℝ] ℝ) →ₗ[ℝ] ℝ) (hL : HessianPositive L)
    (H H0 : E →L[ℝ] E →L[ℝ] ℝ) (D1 D2 D3 : E →L[ℝ] ℝ)
    (C k : ℝ)
    (hbound : ∀ v : E, H v v ≤ H0 v v+C*‖v‖^2-
      k*((D1 v)^2+(D2 v)^2+(D3 v)^2)) :
    L H ≤ L H0+C*L (realInnerForm (E := E))-
      k*(L (dualSquareForm D1)+L (dualSquareForm D2)+L (dualSquareForm D3)) := by
  have hh := hL (H0+C • realInnerForm (E := E)-
      k • (dualSquareForm D1+dualSquareForm D2+dualSquareForm D3)-H) (by
    intro v
    have hb := hbound v
    have hi : realInnerForm (E := E) v v = ‖v‖^2 := by
      change inner ℝ v v = _
      exact real_inner_self_eq_norm_sq v
    simpa only [sub_apply,add_apply,smul_apply,smul_eq_mul,hi,dualSquareForm_apply,pow_two] using
      sub_nonneg.mpr hb)
  change 0 ≤ L (H0+C • realInnerForm (E := E)-
    k • (dualSquareForm D1+dualSquareForm D2+dualSquareForm D3)-H) at hh
  have heq : L (H0+C • realInnerForm (E := E)-
      k • (dualSquareForm D1+dualSquareForm D2+dualSquareForm D3)-H) =
      L H0+C*L (realInnerForm (E := E))-
      k*(L (dualSquareForm D1)+L (dualSquareForm D2)+L (dualSquareForm D3))-L H := by
    rw [map_sub L,map_sub L,map_add L,map_smul L,map_smul L,map_add L,map_add L]
    rfl
  rw [heq] at hh
  linarith

theorem hessian_contraction_of_three_square_bound_elliptic
    (L : (E →L[ℝ] E →L[ℝ] ℝ) →ₗ[ℝ] ℝ) (hL : HessianPositive L)
    {ell Λ C k : ℝ} (hC : 0 ≤ C) (hk : 0 ≤ k)
    (hlow : ∀ v : E, ell*‖v‖^2 ≤ L (realRankOneForm v))
    (htrace : L (realInnerForm (E := E)) ≤ Λ)
    (H H0 : E →L[ℝ] E →L[ℝ] ℝ) (D1 D2 D3 : E →L[ℝ] ℝ)
    (hbound : ∀ v : E, H v v ≤ H0 v v+C*‖v‖^2-
      k*((D1 v)^2+(D2 v)^2+(D3 v)^2)) :
    L H ≤ L H0+C*Λ-k*ell*(‖D1‖^2+‖D2‖^2+‖D3‖^2) := by
  have hh := hessian_contraction_of_three_square_bound L hL H H0 D1 D2 D3 C k hbound
  have h1 := dualSquareForm_contraction_lower L hlow D1
  have h2 := dualSquareForm_contraction_lower L hlow D2
  have h3 := dualSquareForm_contraction_lower L hlow D3
  have hc := mul_le_mul_of_nonneg_left htrace hC
  have he := mul_le_mul_of_nonneg_left (add_le_add (add_le_add h1 h2) h3) hk
  nlinarith only [hh,hc,he]

end PowerConvexity
