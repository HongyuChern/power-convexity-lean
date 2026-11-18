import PowerConvexity.Analysis.ActualInverseGraphTaylorAlgebraFour

/-! # A common inverse-graph cubic remainder from actual common C3 bounds -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_uniform_C3_cubic_taylor_four {rho : E → ℝ} {S M : ℝ}
    (hS : 0 < S) (hM : 0 ≤ M)
    (hreg : ∀ x ∈ closedBall (0 : E) S, ContDiffAt ℝ 3 rho x)
    (hT : ∀ x ∈ closedBall (0 : E) S, ‖fderiv ℝ (realHessian rho) x‖ ≤ M) :
    ∀ x ∈ closedBall (0 : E) S,
      |rho x-secondTaylorPolynomialZero rho x| ≤ M*‖x‖^3 := by
  have hLip (x y : E) (hx : x ∈ closedBall (0 : E) S) (hy : y ∈ closedBall (0 : E) S) :
      ‖realHessian rho x-realHessian rho y‖ ≤ M*‖x-y‖ :=
    Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z hz => (((hreg z hz).fderiv_right (m := 2) (by norm_num)).fderiv_right
        (m := 1) (by norm_num)).differentiableAt (by norm_num))
      hT (convex_closedBall (0 : E) S) hy hx
  intro x hx
  by_cases hx0 : x=0
  · subst x
    simp only [secondTaylorPolynomialZero_value,sub_self,abs_zero,norm_zero]
    norm_num
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hnS : ‖x‖ ≤ S := by simpa only [mem_closedBall,dist_zero_right] using hx
  have hsub : closedBall (0 : E) ‖x‖ ⊆ closedBall 0 S := closedBall_subset_closedBall hnS
  have hbound (y : E) (hy : y ∈ closedBall 0 ‖x‖) :
      ‖realHessian rho y-realHessian rho 0‖ ≤ M*‖x‖ := by
    have hh := hLip y 0 (hsub hy) (mem_closedBall_self hS.le)
    rw [sub_zero] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left
      (by simpa only [mem_closedBall,dist_zero_right] using hy) hM)
  have hh := actual_secondTaylor_error_of_hessian_modulus hn (mul_nonneg hM hn.le)
    (fun y hy => (hreg y (hsub hy)).of_le (by norm_num)) hbound x
    (by simp only [mem_closedBall,dist_zero_right,le_refl])
  exact hh.trans_eq (by ring)

theorem actual_inverse_graph_common_cubic_taylor_four
    {S M G T : ℝ} (hS : 0 < S) (hS1 : S ≤ 1) (hM : 0 ≤ M) (hG : 0 ≤ G) (hT : 0 ≤ T)
    {N : E} (hN : ‖N‖=1) {rho : E → ℝ}
    (hreg : ∀ x ∈ closedBall (0 : E) S, ContDiffAt ℝ 3 rho x)
    (hrho0 : rho 0=0) (hD0 : fderiv ℝ rho 0=0)
    (hHess : ∀ x ∈ closedBall (0 : E) S, ‖realHessian rho x‖ ≤ M)
    (hThird : ∀ x ∈ closedBall (0 : E) S, ‖fderiv ℝ (realHessian rho) x‖ ≤ M) :
    ∀ p : E → ℝ, IsQuadraticPolynomial p →
      ‖fderiv ℝ p 0‖ ≤ G → ‖realHessian p 0‖ ≤ T →
      ∀ x ∈ closedBall (0 : E) S,
        |p (actualInverseGraphFour N rho x)-secondTaylorPolynomialZero (p ∘ actualInverseGraphFour N rho) x|
          ≤ (G*M+M*T+M^2*T)*‖x‖^3 := by
  have hrho2 : ContDiffAt ℝ 2 rho 0 := (hreg 0 (mem_closedBall_self hS.le)).of_le (by norm_num)
  have hTaylor := actual_uniform_C3_cubic_taylor_four hS hM hreg hThird
  intro p hp hpG hpT x hx
  have hx1 : ‖x‖ ≤ 1 := (show ‖x‖ ≤ S from by simpa only [mem_closedBall,dist_zero_right] using hx).trans hS1
  have hrhov : |rho x| ≤ M*‖x‖^2 := by
    have hh := quadratic_remainder_on_closedBall_of_Hessian_bound hM
      (fun y hy => (hreg y hy).of_le (by norm_num)) hHess
      (mem_closedBall_self hS.le) hx
    simpa only [hrho0,hD0,sub_zero,_root_.zero_apply] using hh
  have herror := hTaylor x hx
  have hDp : |fderiv ℝ p 0 N| ≤ G := by
    exact (by simpa only [Real.norm_eq_abs,hN,mul_one] using (fderiv ℝ p 0).le_opNorm N :
      |fderiv ℝ p 0 N| ≤ ‖fderiv ℝ p 0‖).trans hpG
  have hHN : |realHessian p 0 N N| ≤ T := by
    exact (by simpa only [Real.norm_eq_abs,hN,mul_one] using (realHessian p 0).le_opNorm₂ N N :
      |realHessian p 0 N N| ≤ ‖realHessian p 0‖).trans hpT
  have hHx : |realHessian p 0 x N| ≤ T*‖x‖ := by
    have hh : |realHessian p 0 x N| ≤ ‖realHessian p 0‖*‖x‖ := by
      simpa only [Real.norm_eq_abs,hN,mul_one] using (realHessian p 0).le_opNorm₂ x N
    exact hh.trans (mul_le_mul_of_nonneg_right hpT (norm_nonneg x))
  have hterm1 : |-(fderiv ℝ p 0 N)*(rho x-secondTaylorPolynomialZero rho x)| ≤ G*M*‖x‖^3 := by
    rw [abs_mul,abs_neg]
    exact (mul_le_mul hDp herror (abs_nonneg _) hG).trans_eq (by ring)
  have hterm2 : |rho x*realHessian p 0 x N| ≤ M*T*‖x‖^3 := by
    rw [abs_mul]
    exact (mul_le_mul hrhov hHx (abs_nonneg _) (by positivity)).trans_eq (by ring)
  have hpow43 : ‖x‖^4 ≤ ‖x‖^3 := by
    calc
      ‖x‖^4 = ‖x‖^3*‖x‖ := by ring
      _ ≤ ‖x‖^3*1 := mul_le_mul_of_nonneg_left hx1 (by positivity)
      _ = _ := mul_one _
  have hrho2bound : (rho x)^2 ≤ M^2*‖x‖^4 := by
    have hh := pow_le_pow_left₀ (abs_nonneg (rho x)) hrhov 2
    simpa only [sq_abs,mul_pow,← pow_mul,show (2 : ℕ)*2=4 from rfl] using hh
  have hterm3 : |(rho x)^2/2*realHessian p 0 N N| ≤ M^2*T*‖x‖^3 := by
    rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ (rho x)^2/2)]
    have hh := mul_le_mul_of_nonneg_left hHN (by positivity : 0 ≤ (rho x)^2/2)
    have hsq : (rho x)^2/2 ≤ M^2*‖x‖^4 := by nlinarith [sq_nonneg (rho x)]
    apply hh.trans
    calc
      (rho x)^2/2*T ≤ (M^2*‖x‖^4)*T := mul_le_mul_of_nonneg_right hsq hT
      _ = (M^2*T)*‖x‖^4 := by ring
      _ ≤ (M^2*T)*‖x‖^3 := mul_le_mul_of_nonneg_left hpow43 (by positivity)
  rw [actual_inverse_graph_taylor_error_identity_four hrho2 hrho0 hD0 hp]
  apply (abs_add_le _ _).trans
  apply (add_le_add ((abs_sub _ _).trans (add_le_add hterm1 hterm2)) hterm3).trans_eq
  ring

end PowerConvexity
