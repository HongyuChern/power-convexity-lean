import PowerConvexity.Analysis.ActualInverseGraphCommonTaylorFour

/-! # Common original-coordinate expansion constants before the graph and normal -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_inverse_graph_common_remainder_four
    {S K r M beta G T : ℝ}
    (hS : 0 < S) (hS1 : S ≤ 1) (hK : 0 ≤ K)
    (hr : 0 < r) (hM : 0 ≤ M) (hbeta : 0 ≤ beta) (hbeta1 : beta ≤ 1)
    (hG : 0 ≤ G) (hT : 0 ≤ T) :
    ∃ R > 0, R ≤ 1 ∧ ∃ C ≥ 0,
      ∀ N : E, ‖N‖=1 → ∀ rho : E → ℝ,
      (∀ x ∈ closedBall (0 : E) S, ContDiffAt ℝ 3 rho x) →
      rho 0=0 → fderiv ℝ rho 0=0 →
      (∀ x ∈ closedBall (0 : E) S, ‖realHessian rho x‖ ≤ K) →
      (∀ x ∈ closedBall (0 : E) S, ‖fderiv ℝ (realHessian rho) x‖ ≤ K) →
      (∀ x : E, ∀ t : ℝ, rho (x+t • N)=rho x) →
      ∀ p : E → ℝ, IsQuadraticPolynomial p →
      ‖fderiv ℝ p 0‖ ≤ G → ‖realHessian p 0‖ ≤ T → ∀ u : E → ℝ,
      (∀ z : E, 0 ≤ inner ℝ N z → ‖z‖ < r →
        |u (actualGraphShearFour N rho z)-p z| ≤ M*‖z‖^2*‖z‖^beta) →
      ∀ x ∈ closedBall (0 : E) R, 0 ≤ inner ℝ N (actualInverseGraphFour N rho x) →
        |u x-secondTaylorPolynomialZero (p ∘ actualInverseGraphFour N rho) x| ≤ C*‖x‖^2*‖x‖^beta := by
  let L := 1+K
  have hL : 0 < L := by dsimp [L]; linarith
  let Q := G*K+K*T+K^2*T
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  let R := min S (r/(2*L))
  have hR : 0 < R := lt_min hS (div_pos hr (by positivity))
  have hRS : R ≤ S := min_le_left _ _
  have hRr : R ≤ r/(2*L) := min_le_right _ _
  have hR1 : R ≤ 1 := hRS.trans hS1
  refine ⟨R,hR,hR1,M*L^2*L^beta+Q,by positivity,?_⟩
  intro N hN rho hreg hrho0 hD0 hHess hThird hinv
  let Psi := actualInverseGraphFour N rho
  have hTaylor := actual_inverse_graph_common_cubic_taylor_four hS hS1 hK hG hT hN
    hreg hrho0 hD0 hHess hThird
  intro p hp hpG hpT u herr x hx hNx
  let g := p ∘ Psi
  have hxR : ‖x‖ ≤ R := by simpa only [mem_closedBall,dist_zero_right] using hx
  have hx1 : ‖x‖ ≤ 1 := hxR.trans hR1
  have hPx : ‖Psi x‖ ≤ L*‖x‖ := by
    have hrhov : |rho x| ≤ K*‖x‖^2 := by
      have hh := quadratic_remainder_on_closedBall_of_Hessian_bound hK
        (fun y hy => (hreg y hy).of_le (by norm_num)) hHess
        (mem_closedBall_self hS.le) (closedBall_subset_closedBall hRS hx)
      simpa only [hrho0,hD0,sub_zero,_root_.zero_apply] using hh
    have hsquare : ‖x‖^2 ≤ ‖x‖ := by nlinarith [norm_nonneg x]
    calc
      ‖Psi x‖ ≤ ‖x‖+‖rho x • N‖ := by
        simpa only [Psi,actualInverseGraphFour,actualGraphShearFour,neg_smul,sub_eq_add_neg]
          using norm_sub_le x (rho x • N)
      _ = ‖x‖+|rho x| := by rw [norm_smul,Real.norm_eq_abs,hN,mul_one]
      _ ≤ ‖x‖+K*‖x‖^2 := add_le_add (le_refl _) hrhov
      _ ≤ ‖x‖+K*‖x‖ := add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hsquare hK)
      _ = L*‖x‖ := by dsimp [L]; ring
  have hPsmall : ‖Psi x‖ < r := by
    have hLR : L*R ≤ r/2 := by
      calc
        L*R ≤ L*(r/(2*L)) := mul_le_mul_of_nonneg_left hRr hL.le
        _ = r/2 := by field_simp
    exact (hPx.trans ((mul_le_mul_of_nonneg_left hxR hL.le).trans hLR)).trans_lt (by linarith)
  have he := herr (Psi x) hNx hPsmall
  have hInv : actualGraphShearFour N rho (Psi x)=x := (actual_inverse_graph_inverse_four hinv x).2
  rw [hInv] at he
  have hpw : ‖Psi x‖^beta ≤ L^beta*‖x‖^beta := by
    calc
      ‖Psi x‖^beta ≤ (L*‖x‖)^beta := Real.rpow_le_rpow (norm_nonneg _) hPx hbeta
      _ = _ := Real.mul_rpow hL.le (norm_nonneg x)
  have hsq : ‖Psi x‖^2 ≤ L^2*‖x‖^2 := by
    calc
      ‖Psi x‖^2 ≤ (L*‖x‖)^2 := pow_le_pow_left₀ (norm_nonneg _) hPx 2
      _ = L^2*‖x‖^2 := mul_pow L ‖x‖ 2
  have hE : |u x-g x| ≤ (M*L^2*L^beta)*‖x‖^2*‖x‖^beta := by
    calc
      |u x-g x| ≤ M*‖Psi x‖^2*‖Psi x‖^beta := he
      _ ≤ M*(L^2*‖x‖^2)*(L^beta*‖x‖^beta) := by gcongr
      _ = _ := by ring
  have hTaylorX := hTaylor p hp hpG hpT x (closedBall_subset_closedBall hRS hx)
  have hxp : ‖x‖ ≤ ‖x‖^beta := Real.self_le_rpow_of_le_one (norm_nonneg x) hx1 hbeta1
  have hTK : Q*‖x‖^3 ≤ Q*‖x‖^2*‖x‖^beta := by
    calc
      Q*‖x‖^3 = (Q*‖x‖^2)*‖x‖ := by ring
      _ ≤ (Q*‖x‖^2)*‖x‖^beta := mul_le_mul_of_nonneg_left hxp (by positivity)
  calc
    |u x-secondTaylorPolynomialZero g x| ≤ |u x-g x|+|g x-secondTaylorPolynomialZero g x| :=
      abs_sub_le (u x) (g x) (secondTaylorPolynomialZero g x)
    _ ≤ (M*L^2*L^beta)*‖x‖^2*‖x‖^beta+Q*‖x‖^2*‖x‖^beta := add_le_add hE (hTaylorX.trans hTK)
    _ = (M*L^2*L^beta+Q)*‖x‖^2*‖x‖^beta := by ring

end PowerConvexity
