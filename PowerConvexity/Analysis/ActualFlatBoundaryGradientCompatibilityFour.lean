import PowerConvexity.Analysis.ActualFlatBoundaryQuadraticJetBoundFour

/-! # Actual first-jet compatibility derived from overlapping value remainders -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_quadratic_gradient_difference_bound_four {q : E → ℝ} (hq : IsQuadraticPolynomial q)
    {T : ℝ} (hH : ‖realHessian q 0‖ ≤ T) (x y : E) :
    ‖fderiv ℝ q x-fderiv ℝ q y‖ ≤ T*‖x-y‖ := by
  have he : fderiv ℝ q x-fderiv ℝ q y=realHessian q 0 (x-y) := by
    rw [quadratic_fderiv_from_jet_zero hq x,quadratic_fderiv_from_jet_zero hq y,map_sub]
    abel
  rw [he]
  exact ((realHessian q 0).le_opNorm _).trans (mul_le_mul_of_nonneg_right hH (norm_nonneg _))

theorem actual_halfspace_quadratic_gradient_comparison_four {N x y : E}
    (hN : ‖N‖=1) (hx : 0 ≤ inner ℝ N x) {s C T : ℝ} (hs : 0 < s)
    (hxy : ‖x-y‖ ≤ s/4) (hC : 0 ≤ C) {u p q : E → ℝ}
    (hp : IsQuadraticPolynomial p) (hq : IsQuadraticPolynomial q) (hqH : ‖realHessian q 0‖ ≤ T)
    (hpE : ∀ z : E, 0 ≤ inner ℝ N z → ‖z-x‖ ≤ s → |u z-p z| ≤ C*s^2)
    (hqE : ∀ z : E, 0 ≤ inner ℝ N z → ‖z-y‖ ≤ s → |u z-q z| ≤ C*s^2) :
    ‖fderiv ℝ p x-fderiv ℝ q y‖ ≤ 272*C*s+T*‖x-y‖ := by
  have hd := IsQuadraticPolynomial_sub hp hq
  have hb : ∀ z : E, 0 ≤ inner ℝ N z → ‖z-x‖ ≤ s/2 → |p z-q z| ≤ 2*C*s^2 := by
    intro z hz hzx
    have hzy : ‖z-y‖ ≤ s := by
      have hh : ‖z-y‖ ≤ ‖z-x‖+‖x-y‖ := by simpa only [dist_eq_norm] using dist_triangle z x y
      linarith
    have hh := abs_sub_le (p z) (u z) (q z)
    rw [abs_sub_comm (p z) (u z)] at hh
    exact (hh.trans (add_le_add (hpE z hz (by linarith)) (hqE z hz hzy))).trans_eq (by ring)
  have hgrad := actual_halfspace_quadratic_absolute_gradient_four hN hx (half_pos hs)
    (by positivity : 0 ≤ 2*C*s^2) hd hb
  have heD : fderiv ℝ (fun z => p z-q z) x=fderiv ℝ p x-fderiv ℝ q x :=
    fderiv_fun_sub ((IsQuadraticPolynomial_contDiff hp 1).contDiffAt.differentiableAt (by norm_num))
      ((IsQuadraticPolynomial_contDiff hq 1).contDiffAt.differentiableAt (by norm_num))
  rw [heD] at hgrad
  have hgrad' : ‖fderiv ℝ p x-fderiv ℝ q x‖ ≤ 272*C*s := hgrad.trans_eq (by field_simp <;> ring)
  have hh : ‖fderiv ℝ p x-fderiv ℝ q y‖ ≤ ‖fderiv ℝ p x-fderiv ℝ q x‖+‖fderiv ℝ q x-fderiv ℝ q y‖ := by
    simpa only [dist_eq_norm] using dist_triangle (fderiv ℝ p x) (fderiv ℝ q x) (fderiv ℝ q y)
  exact hh.trans (add_le_add hgrad' (actual_quadratic_gradient_difference_bound_four hq hqH x y))

theorem actual_halfspace_quadratic_field_gradient_lipschitz_four {N : E} (hN : ‖N‖=1)
    {V : Set E} (hV : ∀ x ∈ V, 0 ≤ inner ℝ N x) {u : E → ℝ} {P : E → E → ℝ}
    {R gamma M T : ℝ} (hR : 0 < R) (hR1 : R ≤ 1) (hg : 0 ≤ gamma) (hM : 0 ≤ M)
    (hP : ∀ x ∈ V, IsQuadraticPolynomial (P x))
    (hH : ∀ x ∈ V, ‖realHessian (P x) 0‖ ≤ T)
    (herr : ∀ c ∈ V, ∀ z : E, 0 ≤ inner ℝ N z → ‖z-c‖ < R/2 →
      |u z-P c z| ≤ M*‖z-c‖^2*‖z-c‖^gamma) :
    ∀ x ∈ V, ∀ y ∈ V, ‖x-y‖ < R/8 →
      ‖fderiv ℝ (P x) x-fderiv ℝ (P y) y‖ ≤ (1088*M+T)*‖x-y‖ := by
  intro x hx y hy hnear
  by_cases hxy : x=y
  · subst y
    simp only [sub_self,norm_zero,mul_zero,le_refl]
  have hd : 0 < ‖x-y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  let s := 4*‖x-y‖
  have hs : 0 < s := by dsimp only [s]; positivity
  have hsR : s < R/2 := by dsimp only [s]; linarith
  have hs1 : s ≤ 1 := by linarith
  have hpw : s^gamma ≤ 1 := Real.rpow_le_one hs.le hs1 hg
  have herror (c : E) (hc : c ∈ V) (z : E) (hz : 0 ≤ inner ℝ N z) (hzc : ‖z-c‖ ≤ s) :
      |u z-P c z| ≤ (M*s^gamma)*s^2 := by
    calc
      _ ≤ M*‖z-c‖^2*‖z-c‖^gamma := herr c hc z hz (hzc.trans_lt hsR)
      _ ≤ M*s^2*s^gamma := by gcongr
      _ = _ := by ring
  have hh := actual_halfspace_quadratic_gradient_comparison_four hN (hV x hx) hs
    (by dsimp only [s]; linarith : ‖x-y‖ ≤ s/4) (by positivity : 0 ≤ M*s^gamma)
    (hP x hx) (hP y hy) (hH y hy) (herror x hx) (herror y hy)
  apply hh.trans
  have hf : M*s^gamma ≤ M := (mul_le_mul_of_nonneg_left hpw hM).trans_eq (mul_one M)
  calc
    272*(M*s^gamma)*s+T*‖x-y‖ ≤ 272*M*s+T*‖x-y‖ := by gcongr
    _ = _ := by dsimp only [s]; ring

end PowerConvexity
