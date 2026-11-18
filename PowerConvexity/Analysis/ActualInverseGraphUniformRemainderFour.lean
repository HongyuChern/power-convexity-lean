import PowerConvexity.Analysis.ActualInverseGraphUniformTaylorFour

/-! # Uniform original-coordinate expansion constants before the boundary polynomial -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_inverse_graph_uniform_remainder_four {N : E} (hN : ‖N‖=1)
    {rho : E → ℝ} {r M beta G T : ℝ}
    (hr : 0 < r) (hM : 0 ≤ M) (hbeta : 0 ≤ beta) (hbeta1 : beta ≤ 1)
    (hG : 0 ≤ G) (hT : 0 ≤ T)
    (hrho : ContDiffAt ℝ 3 rho 0) (hrho0 : rho 0=0) (hD0 : fderiv ℝ rho 0=0)
    (hinv : ∀ x : E, ∀ t : ℝ, rho (x+t • N)=rho x) :
    ∃ R > 0, R ≤ 1 ∧ ∃ C ≥ 0, ∀ p : E → ℝ, IsQuadraticPolynomial p →
      ‖fderiv ℝ p 0‖ ≤ G → ‖realHessian p 0‖ ≤ T → ∀ u : E → ℝ,
      (∀ z : E, 0 ≤ inner ℝ N z → ‖z‖ < r →
        |u (actualGraphShearFour N rho z)-p z| ≤ M*‖z‖^2*‖z‖^beta) →
      ∀ x ∈ closedBall (0 : E) R, 0 ≤ inner ℝ N (actualInverseGraphFour N rho x) →
        |u x-secondTaylorPolynomialZero (p ∘ actualInverseGraphFour N rho) x| ≤ C*‖x‖^2*‖x‖^beta := by
  let Psi := actualInverseGraphFour N rho
  have hPsi0 : Psi 0=0 := actual_inverse_graph_value_four hrho0
  have hPsi : ContDiffAt ℝ 3 Psi 0 := actual_inverse_graph_contDiffAt_four hrho
  obtain ⟨Rt,hRt,hRt1,K,hK,hTaylor⟩ :=
    actual_inverse_graph_uniform_cubic_taylor_four hN hrho hrho0 hD0 hG hT
  obtain ⟨Rl,hRl,_,L0,hL0,hLip⟩ := actual_C1_closed_ball_lipschitz_four
    (hPsi.of_le (by norm_num : (1 : ℕ∞ω) ≤ 3))
  let L := L0+1
  have hL : 0 < L := by dsimp [L]; linarith
  let R := min Rt (min Rl (r/(2*L)))
  have hR : 0 < R := lt_min hRt (lt_min hRl (div_pos hr (by positivity)))
  have hRRt : R ≤ Rt := min_le_left _ _
  have hRRl : R ≤ Rl := (min_le_right _ _).trans (min_le_left _ _)
  have hRr : R ≤ r/(2*L) := (min_le_right _ _).trans (min_le_right _ _)
  have hR1 : R ≤ 1 := hRRt.trans hRt1
  refine ⟨R,hR,hR1,M*L^2*L^beta+K,by positivity,?_⟩
  intro p hp hpG hpT u herr x hx hNx
  let g := p ∘ Psi
  have hxR : ‖x‖ ≤ R := by simpa only [mem_closedBall,dist_zero_right] using hx
  have hx1 : ‖x‖ ≤ 1 := hxR.trans hR1
  have hPx : ‖Psi x‖ ≤ L*‖x‖ := by
    have hh := hLip x (closedBall_subset_closedBall hRRl hx) 0 (mem_closedBall_self hRl.le)
    rw [hPsi0,sub_zero,sub_zero] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (by dsimp [L]; linarith) (norm_nonneg x))
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
  have hTaylorX := hTaylor p hp hpG hpT x (closedBall_subset_closedBall hRRt hx)
  have hxp : ‖x‖ ≤ ‖x‖^beta := Real.self_le_rpow_of_le_one (norm_nonneg x) hx1 hbeta1
  have hTK : K*‖x‖^3 ≤ K*‖x‖^2*‖x‖^beta := by
    calc
      K*‖x‖^3 = (K*‖x‖^2)*‖x‖ := by ring
      _ ≤ (K*‖x‖^2)*‖x‖^beta := mul_le_mul_of_nonneg_left hxp (by positivity)
  calc
    |u x-secondTaylorPolynomialZero g x| ≤ |u x-g x|+|g x-secondTaylorPolynomialZero g x| :=
      abs_sub_le (u x) (g x) (secondTaylorPolynomialZero g x)
    _ ≤ (M*L^2*L^beta)*‖x‖^2*‖x‖^beta+K*‖x‖^2*‖x‖^beta := add_le_add hE (hTaylorX.trans hTK)
    _ = (M*L^2*L^beta+K)*‖x‖^2*‖x‖^beta := by ring

end PowerConvexity
