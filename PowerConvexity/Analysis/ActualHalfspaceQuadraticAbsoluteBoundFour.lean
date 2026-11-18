import PowerConvexity.Analysis.ActualHalfspaceQuadraticProbeFour

/-! # Uniform quadratic jet bounds from actual values on a half-ball -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_halfspace_quadratic_absolute_hessian_four {N c : E}
    (hN : ‖N‖=1) (hc : 0 ≤ inner ℝ N c) {R B : ℝ} (hR : 0 < R) (hB : 0 ≤ B)
    {q : E → ℝ} (hq : IsQuadraticPolynomial q)
    (hbound : ∀ x : E, 0 ≤ inner ℝ N x → ‖x-c‖ ≤ R → |q x| ≤ B) :
    ∀ x : E, ‖realHessian q x‖ ≤ 128*B/R^2 := by
  let y := c+(R/2) • N
  have hsup : ∀ w ∈ closedBall (0 : E) (R/4), |q (y+w)| ≤ (16*B/R^2)*(R/4)^2 := by
    intro w hw
    obtain ⟨hz,hzc,hzy⟩ := actual_halfspace_shared_probe_four (y := c) hN hc hR
      (by simpa only [sub_self,norm_zero] using (by positivity : (0 : ℝ) ≤ R/4)) hw
    exact (hbound _ hz hzc).trans_eq (by field_simp <;> ring)
  have hh := (actual_quadratic_scaled_sup_jets_at_four hq y (by positivity : 0 < R/4)
    (by positivity : 0 ≤ 16*B/R^2) hsup).2.2
  intro x
  rw [quadratic_realHessian_from_jet_zero hq y] at hh
  rw [quadratic_realHessian_from_jet_zero hq x]
  exact hh.trans_eq (by ring)

theorem actual_halfspace_quadratic_absolute_gradient_four {N c : E}
    (hN : ‖N‖=1) (hc : 0 ≤ inner ℝ N c) {R B : ℝ} (hR : 0 < R) (hB : 0 ≤ B)
    {q : E → ℝ} (hq : IsQuadraticPolynomial q)
    (hbound : ∀ x : E, 0 ≤ inner ℝ N x → ‖x-c‖ ≤ R → |q x| ≤ B) :
    ‖fderiv ℝ q c‖ ≤ 68*B/R := by
  let y := c+(R/2) • N
  have hsup : ∀ w ∈ closedBall (0 : E) (R/4), |q (y+w)| ≤ (16*B/R^2)*(R/4)^2 := by
    intro w hw
    obtain ⟨hz,hzc,hzy⟩ := actual_halfspace_shared_probe_four (y := c) hN hc hR
      (by simpa only [sub_self,norm_zero] using (by positivity : (0 : ℝ) ≤ R/4)) hw
    exact (hbound _ hz hzc).trans_eq (by field_simp <;> ring)
  have hjet := actual_quadratic_scaled_sup_jets_at_four hq y (by positivity : 0 < R/4)
    (by positivity : 0 ≤ 16*B/R^2) hsup
  have hgrad : ‖fderiv ℝ q y‖ ≤ 4*B/R := hjet.2.1.trans_eq (by field_simp <;> ring)
  have hess := actual_halfspace_quadratic_absolute_hessian_four hN hc hR hB hq hbound 0
  have he : fderiv ℝ q c=fderiv ℝ q y+realHessian q 0 (c-y) := by
    rw [quadratic_fderiv_from_jet_zero hq c,quadratic_fderiv_from_jet_zero hq y,map_sub]
    abel
  have hn : ‖c-y‖=R/2 := by
    have he : c-y=-((R/2) • N) := by dsimp only [y]; abel
    rw [he,norm_neg,norm_smul,Real.norm_eq_abs,abs_of_pos (half_pos hR),hN,mul_one]
  rw [he]
  calc
    _ ≤ ‖fderiv ℝ q y‖+‖realHessian q 0 (c-y)‖ := norm_add_le _ _
    _ ≤ 4*B/R+(128*B/R^2)*‖c-y‖ := add_le_add hgrad
      (((realHessian q 0).le_opNorm _).trans (mul_le_mul_of_nonneg_right hess (norm_nonneg _)))
    _ = _ := by rw [hn]; field_simp <;> ring

end PowerConvexity
