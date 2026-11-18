import PowerConvexity.Analysis.ActualBoundaryDistanceBallFour
import PowerConvexity.Analysis.ActualHalfspaceQuadraticProbeFour

/-! # An actual interior probe ball from a convex domain's fixed inball -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_convex_boundary_probe_ball_four {U : Set E} (hU : IsOpen U)
    (hconv : Convex ℝ U) {o c : E} {rho theta : ℝ}
    (hball : closedBall o rho ⊆ U) (hc : c ∈ closure U)
    (htheta : 0 < theta) (htheta1 : theta ≤ 1) :
    ∀ w ∈ closedBall (0 : E) (theta*rho), c+theta • (o-c)+w ∈ U := by
  intro w hw
  have hwN : ‖w‖ ≤ theta*rho := by simpa only [mem_closedBall,dist_zero_right] using hw
  have hz : o+theta⁻¹ • w ∈ closedBall o rho := by
    rw [mem_closedBall,dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr htheta)]
    have hh := mul_le_mul_of_nonneg_left hwN (inv_pos.mpr htheta).le
    simpa only [← mul_assoc,inv_mul_cancel₀ htheta.ne',one_mul] using hh
  have hzI : o+theta⁻¹ • w ∈ interior U := by rw [hU.interior_eq]; exact hball hz
  have hh := hconv.combo_closure_interior_mem_interior hc hzI
    (show 0 ≤ 1-theta by linarith) htheta (show (1-theta)+theta=1 by ring)
  have he : (1-theta) • c+theta • (o+theta⁻¹ • w)=c+theta • (o-c)+w := by
    simp only [smul_add,smul_sub,sub_smul,one_smul,smul_smul,
      mul_inv_cancel₀ htheta.ne',one_smul]
    abel
  rw [he,hU.interior_eq] at hh
  exact hh

theorem actual_convex_boundary_shared_probe_four {U : Set E} (hU : IsOpen U)
    (hconv : Convex ℝ U) {o c d : E} {rho D s : ℝ}
    (hrho : 0 < rho) (hD : 0 ≤ D) (hs : 0 < s) (hsD : s ≤ 4*(D+rho))
    (hball : closedBall o rho ⊆ U) (hc : c ∈ closure U)
    (hco : ‖o-c‖ ≤ D) (hcd : ‖c-d‖ ≤ s/4) :
    let theta := s/(4*(D+rho))
    let a := c+theta • (o-c)
    ∀ w ∈ closedBall (0 : E) (theta*rho),
      a+w ∈ U ∧ ‖(a+w)-c‖ ≤ s ∧ ‖(a+w)-d‖ ≤ s := by
  dsimp only
  let theta := s/(4*(D+rho))
  have hden : 0 < 4*(D+rho) := by positivity
  have ht : 0 < theta := div_pos hs hden
  have ht1 : theta ≤ 1 := (div_le_one hden).mpr hsD
  have htotal : theta*(D+rho)=s/4 := by dsimp [theta]; field_simp
  intro w hw
  have hwN : ‖w‖ ≤ theta*rho := by simpa only [mem_closedBall,dist_zero_right] using hw
  have hnc : ‖(c+theta • (o-c)+w)-c‖ ≤ s/4 := by
    have he : (c+theta • (o-c)+w)-c=theta • (o-c)+w := by abel
    rw [he]
    apply (norm_add_le (theta • (o-c)) w).trans
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos ht]
    have hh := mul_le_mul_of_nonneg_left hco ht.le
    nlinarith [htotal]
  refine ⟨actual_convex_boundary_probe_ball_four hU hconv hball hc ht ht1 w hw,hnc.trans (by linarith),?_⟩
  have hh : ‖(c+theta • (o-c)+w)-d‖ ≤ ‖(c+theta • (o-c)+w)-c‖+‖c-d‖ := by
    simpa only [dist_eq_norm] using dist_triangle (c+theta • (o-c)+w) c d
  linarith

end PowerConvexity
