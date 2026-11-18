import PowerConvexity.Analysis.ActualFlatResidualEquationFour

/-! # The actual first jet of a quadratic vanishing on a flat hyperplane -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix
open scoped ContDiff Topology InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
local notation "E" => DeGiorgi.AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_flat_quadratic_fderiv_tangent_zero_four {N : E} {q : E → ℝ}
    (hq : IsQuadraticPolynomial q) (hq0 : ∀ x : E, inner ℝ N x=0 → q x=0)
    {v : E} (hv : inner ℝ N v=0) : fderiv ℝ q 0 v=0 := by
  have hz := hq0 0 (by simp)
  have hnv : inner ℝ N (-v)=0 := by simp only [inner_neg_right,hv,neg_zero]
  have hp := quadratic_exact_Taylor hq 0 v
  have hm := quadratic_exact_Taylor hq 0 (-v)
  simp only [sub_zero,hq0 v hv,hq0 (-v) hnv,hz,map_neg,_root_.neg_apply,neg_neg,zero_add] at hp hm
  linarith

theorem actual_flat_quadratic_fderiv_normal_four {N : E} (hN : ‖N‖=1) {q : E → ℝ}
    (hq : IsQuadraticPolynomial q) (hq0 : ∀ x : E, inner ℝ N x=0 → q x=0) (v : E) :
    fderiv ℝ q 0 v = inner ℝ N v*fderiv ℝ q 0 N := by
  have hv : inner ℝ N (v-inner ℝ N v • N)=0 := by
    simp only [inner_sub_right,inner_smul_right,real_inner_self_eq_norm_sq,hN,one_pow,mul_one,sub_self]
  have hh := actual_flat_quadratic_fderiv_tangent_zero_four hq hq0 hv
  simpa only [map_sub,map_smul,smul_eq_mul,sub_eq_zero] using hh

theorem actual_flat_quadratic_fderiv_norm_four {N : E} (hN : ‖N‖=1) {q : E → ℝ}
    (hq : IsQuadraticPolynomial q) (hq0 : ∀ x : E, inner ℝ N x=0 → q x=0) :
    ‖fderiv ℝ q 0‖ ≤ |fderiv ℝ q 0 N| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (abs_nonneg _)
  intro v
  rw [Real.norm_eq_abs,actual_flat_quadratic_fderiv_normal_four hN hq hq0,abs_mul]
  have hi : |inner ℝ N v| ≤ ‖v‖ := by
    simpa only [hN,one_mul] using abs_real_inner_le_norm N v
  exact (mul_le_mul_of_nonneg_right hi (abs_nonneg _)).trans_eq (mul_comm _ _)

theorem actual_flat_quadratic_gradient_from_normal_value_four {N : E} (hN : ‖N‖=1)
    {q : E → ℝ} (hq : IsQuadraticPolynomial q)
    (hq0 : ∀ x : E, inner ℝ N x=0 → q x=0)
    {r K M : ℝ} (hr : 0 < r) (hval : |q (r • N)| ≤ K)
    (hH : ‖realHessian q 0‖ ≤ M) :
    ‖fderiv ℝ q 0‖ ≤ (K+r^2*M/2)/r := by
  have hz := hq0 0 (by simp)
  have ht := quadratic_exact_Taylor hq 0 (r • N)
  simp only [sub_zero,hz,zero_add,map_smul,_root_.smul_apply,smul_eq_mul] at ht
  have he : r*fderiv ℝ q 0 N=q (r • N)-(r^2/2)*realHessian q 0 N N := by nlinarith only [ht]
  have hn : |realHessian q 0 N N| ≤ M :=
    (by simpa only [Real.norm_eq_abs,hN,mul_one] using (realHessian q 0).le_opNorm₂ N N :
      |realHessian q 0 N N| ≤ ‖realHessian q 0‖).trans hH
  have hb : |r*fderiv ℝ q 0 N| ≤ K+r^2*M/2 := by
    rw [he]
    apply (abs_sub _ _).trans
    apply add_le_add hval
    rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ r^2/2)]
    exact (mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ r^2/2)).trans_eq (by ring)
  rw [abs_mul,abs_of_pos hr] at hb
  apply (actual_flat_quadratic_fderiv_norm_four hN hq hq0).trans
  apply (le_div_iff₀ hr).mpr
  nlinarith only [hb]

end PowerConvexity
