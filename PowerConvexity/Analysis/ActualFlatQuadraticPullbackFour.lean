import PowerConvexity.Analysis.ActualFlatUniformCenteredExpansionFour
import PowerConvexity.Analysis.ActualPhysicalQuadraticTwo

/-! # Returning the centred half-space expansion to the actual physical ball -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_centered_inverse_coordinates_four (G : E ≃L[ℝ] E) (c : E)
    {r : ℝ} (hr : 0 < r) (x : E) :
    c+G (r • (r⁻¹ • (G.symm x-G.symm c)))=x := by
  rw [smul_smul,mul_inv_cancel₀ hr.ne',one_smul,map_sub,G.apply_symm_apply,G.apply_symm_apply]
  abel

theorem actual_centered_inverse_norm_four (G : E ≃L[ℝ] E) (c : E)
    {r L : ℝ} (hr : 0 < r) (hG : ‖G.symm.toContinuousLinearMap‖ ≤ L) (x : E) :
    ‖r⁻¹ • (G.symm x-G.symm c)‖ ≤ (L/r)*‖x-c‖ := by
  rw [← map_sub,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
  have hh := (G.symm.toContinuousLinearMap.le_opNorm (x-c)).trans
    (mul_le_mul_of_nonneg_right hG (norm_nonneg _))
  exact (mul_le_mul_of_nonneg_left hh (inv_pos.mpr hr).le).trans_eq (by ring)

theorem actual_centered_inverse_halfspace_four {N c x : E} (G : E ≃L[ℝ] E)
    {r k : ℝ} (hr : 0 < r) (hk : 0 < k) (hc : inner ℝ N c=0)
    (hN : ∀ v : E, inner ℝ N (G v)=k*inner ℝ N v) (hx : 0 ≤ inner ℝ N x) :
    0 ≤ inner ℝ N (r⁻¹ • (G.symm x-G.symm c)) := by
  have hh := hN (G.symm x-G.symm c)
  rw [map_sub,G.apply_symm_apply,G.apply_symm_apply,inner_sub_right,hc,sub_zero] at hh
  have hi : 0 ≤ inner ℝ N (G.symm x-G.symm c) := by nlinarith
  rw [inner_smul_right]
  exact mul_nonneg (inv_pos.mpr hr).le hi

theorem actual_centered_inverse_plane_four {N c x : E} (G : E ≃L[ℝ] E)
    {r k : ℝ} (hk : 0 < k) (hc : inner ℝ N c=0)
    (hN : ∀ v : E, inner ℝ N (G v)=k*inner ℝ N v) (hx : inner ℝ N x=0) :
    inner ℝ N (r⁻¹ • (G.symm x-G.symm c))=0 := by
  have hh := hN (G.symm x-G.symm c)
  rw [map_sub,G.apply_symm_apply,G.apply_symm_apply,inner_sub_right,hc,hx,sub_self] at hh
  have hi : inner ℝ N (G.symm x-G.symm c)=0 := by nlinarith
  rw [inner_smul_right,hi,mul_zero]

theorem actual_flat_physical_quadratic_zero_four {N c : E} (G : E ≃L[ℝ] E)
    {r k : ℝ} (hk : 0 < k) (hc : inner ℝ N c=0)
    (hN : ∀ v : E, inner ℝ N (G v)=k*inner ℝ N v) {p : E → ℝ}
    (hp : ∀ z : E, inner ℝ N z=0 → p z=0) :
    ∀ x : E, inner ℝ N x=0 → actualPhysicalQuadraticTwo G (G.symm c) r p x=0 := by
  intro x hx
  exact hp _ (actual_centered_inverse_plane_four G hk hc hN hx)

theorem actual_flat_physical_quadratic_error_four {N c : E} (G : E ≃L[ℝ] E)
    {r R s k L C : ℝ} (hr : 0 < r) (hL : 0 < L) (hk : 0 < k)
    (hc : inner ℝ N c=0) (hN : ∀ v : E, inner ℝ N (G v)=k*inner ℝ N v)
    (hInv : ‖G.symm.toContinuousLinearMap‖ ≤ L) {u p : E → ℝ}
    (herr : ∀ n : ℕ, ∀ z ∈ actualFlatClosedUpperBallFour N (R*s^n),
      |u (c+G (r • z))-p z| ≤ C*(1/2 : ℝ)^n*(R*s^n)^2) :
    ∀ n : ℕ, ∀ x : E, 0 ≤ inner ℝ N x → ‖x-c‖ ≤ (r*R/L)*s^n →
      |u x-actualPhysicalQuadraticTwo G (G.symm c) r p x| ≤
        (C*(L/r)^2)*(1/2 : ℝ)^n*((r*R/L)*s^n)^2 := by
  intro n x hx hxc
  let z := r⁻¹ • (G.symm x-G.symm c)
  have hz : z ∈ actualFlatClosedUpperBallFour N (R*s^n) := by
    constructor
    · rw [mem_closedBall,dist_zero_right]
      calc
        ‖z‖ ≤ (L/r)*‖x-c‖ := actual_centered_inverse_norm_four G c hr hInv x
        _ ≤ (L/r)*((r*R/L)*s^n) := mul_le_mul_of_nonneg_left hxc (div_pos hL hr).le
        _ = R*s^n := by field_simp
    · exact actual_centered_inverse_halfspace_four G hr hk hc hN hx
  have hh := herr n z hz
  rw [actual_centered_inverse_coordinates_four G c hr x] at hh
  exact hh.trans_eq (by field_simp)

end PowerConvexity
