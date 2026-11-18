import PowerConvexity.Analysis.ActualInverseGraphTaylorAlgebraFour

/-! # Uniform inverse-graph Taylor errors: the radius and constant precede the polynomial -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_inverse_graph_uniform_cubic_taylor_four {N : E} (hN : ‖N‖=1)
    {rho : E → ℝ} (hrho : ContDiffAt ℝ 3 rho 0) (hrho0 : rho 0=0) (hD0 : fderiv ℝ rho 0=0)
    {G T : ℝ} (hG : 0 ≤ G) (hT : 0 ≤ T) :
    ∃ R > 0, R ≤ 1 ∧ ∃ C ≥ 0, ∀ p : E → ℝ, IsQuadraticPolynomial p →
      ‖fderiv ℝ p 0‖ ≤ G → ‖realHessian p 0‖ ≤ T →
      ∀ x ∈ closedBall (0 : E) R,
        |p (actualInverseGraphFour N rho x)-secondTaylorPolynomialZero (p ∘ actualInverseGraphFour N rho) x|
          ≤ C*‖x‖^3 := by
  have hrho2 : ContDiffAt ℝ 2 rho 0 := hrho.of_le (by norm_num)
  obtain ⟨Rt,hRt,hRt1,K,hK,hTaylor⟩ := actual_local_cubic_taylor_four hrho
  obtain ⟨A,hA,Ra,hRa,hreg,hH⟩ := exists_local_uniform_Hessian_bound hrho2
  let R := min Rt Ra
  have hR : 0 < R := lt_min hRt hRa
  have hRRt : R ≤ Rt := min_le_left _ _
  have hRRa : R ≤ Ra := min_le_right _ _
  have hR1 : R ≤ 1 := hRRt.trans hRt1
  refine ⟨R,hR,hR1,G*K+A*T+A^2*T,by positivity,?_⟩
  intro p hp hpG hpT x hx
  have hx1 : ‖x‖ ≤ 1 := (show ‖x‖ ≤ R from by simpa only [mem_closedBall,dist_zero_right] using hx).trans hR1
  have hrhov : |rho x| ≤ A*‖x‖^2 := by
    have hh := quadratic_remainder_on_closedBall_of_Hessian_bound hA.le hreg hH
      (mem_closedBall_self hRa.le) (closedBall_subset_closedBall hRRa hx)
    simpa only [hrho0,hD0,sub_zero,_root_.zero_apply] using hh
  have herror := hTaylor x (closedBall_subset_closedBall hRRt hx)
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
  have hterm1 : |-(fderiv ℝ p 0 N)*(rho x-secondTaylorPolynomialZero rho x)| ≤ G*K*‖x‖^3 := by
    rw [abs_mul,abs_neg]
    exact (mul_le_mul hDp herror (abs_nonneg _) hG).trans_eq (by ring)
  have hterm2 : |rho x*realHessian p 0 x N| ≤ A*T*‖x‖^3 := by
    rw [abs_mul]
    exact (mul_le_mul hrhov hHx (abs_nonneg _) (by positivity)).trans_eq (by ring)
  have hpow43 : ‖x‖^4 ≤ ‖x‖^3 := by
    calc
      ‖x‖^4 = ‖x‖^3*‖x‖ := by ring
      _ ≤ ‖x‖^3*1 := mul_le_mul_of_nonneg_left hx1 (by positivity)
      _ = _ := mul_one _
  have hrho2bound : (rho x)^2 ≤ A^2*‖x‖^4 := by
    have hh := pow_le_pow_left₀ (abs_nonneg (rho x)) hrhov 2
    simpa only [sq_abs,mul_pow,← pow_mul,show (2 : ℕ)*2=4 from rfl] using hh
  have hterm3 : |(rho x)^2/2*realHessian p 0 N N| ≤ A^2*T*‖x‖^3 := by
    rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ (rho x)^2/2)]
    have hh := mul_le_mul_of_nonneg_left hHN (by positivity : 0 ≤ (rho x)^2/2)
    have hsq : (rho x)^2/2 ≤ A^2*‖x‖^4 := by nlinarith [sq_nonneg (rho x)]
    apply hh.trans
    calc
      (rho x)^2/2*T ≤ (A^2*‖x‖^4)*T := mul_le_mul_of_nonneg_right hsq hT
      _ = (A^2*T)*‖x‖^4 := by ring
      _ ≤ (A^2*T)*‖x‖^3 := mul_le_mul_of_nonneg_left hpow43 (by positivity)
  rw [actual_inverse_graph_taylor_error_identity_four hrho2 hrho0 hD0 hp]
  apply (abs_add_le _ _).trans
  apply (add_le_add ((abs_sub _ _).trans (add_le_add hterm1 hterm2)) hterm3).trans_eq
  ring

end PowerConvexity
