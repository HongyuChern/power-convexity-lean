import PowerConvexity.Analysis.ActualInverseGraphJetFour
import PowerConvexity.Calculus.UniformQuadraticRemainder

/-! # A common first-order remainder in the original graph coordinates

The inverse shear transports the proven quotient remainder to an actual
affine approximation. The common radius and constant precede the graph.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_uniform_inverse_graph_linear_remainder_four
    {r C Q M alpha : ℝ} (hr : 0 < r) (hC : 0 ≤ C) (hQ : 0 ≤ Q) (hM : 0 ≤ M)
    (ha : 0 ≤ alpha) (ha1 : alpha ≤ 1) :
    ∃ R > 0, R ≤ 1 ∧ ∃ K ≥ 0, ∀ N : E, ‖N‖=1 →
      ∀ rho u : E → ℝ, ∀ q : ℝ, |q| ≤ Q →
      (∀ x ∈ closedBall (0 : E) 1, ContDiffAt ℝ 2 rho x) →
      (∀ x ∈ closedBall (0 : E) 1, ‖realHessian rho x‖ ≤ M) →
      rho 0=0 → fderiv ℝ rho 0=0 →
      (∀ x : E, ∀ t : ℝ, rho (x+t • N)=rho x) →
      (∀ z ∈ actualFlatClosedUpperBallFour N r,
        |u (actualGraphShearFour N rho z)-q*inner ℝ N z| ≤ C*‖z‖^alpha*inner ℝ N z) →
      ∀ x ∈ closedBall (0 : E) R,
      0 ≤ inner ℝ N (actualInverseGraphFour N rho x) →
        |u x-q*inner ℝ N x| ≤ K*‖x‖*‖x‖^alpha := by
  let L := 1+M
  have hL : 0 < L := by dsimp only [L]; positivity
  let R := min 1 (r/L)
  have hR : 0 < R := lt_min zero_lt_one (div_pos hr hL)
  have hR1 : R ≤ 1 := min_le_left _ _
  have hRr : L*R ≤ r := by
    have hh := (le_div_iff₀ hL).mp (min_le_right (1 : ℝ) (r/L))
    nlinarith
  let K := C*L*L^alpha+Q*M
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨R,hR,hR1,K,hK,?_⟩
  intro N hN rho u q hq hrho hH hrho0 hD0 hinv herr x hx hside
  have hx1 : x ∈ closedBall (0 : E) 1 := closedBall_subset_closedBall hR1 hx
  have hnorm1 : ‖x‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using hx1
  have hnormR : ‖x‖ ≤ R := by simpa only [mem_closedBall,dist_zero_right] using hx
  have hrhov : |rho x| ≤ M*‖x‖^2 := by
    have hh := quadratic_remainder_on_closedBall_of_Hessian_bound hM hrho hH
      (mem_closedBall_self (by norm_num : (0 : ℝ) ≤ 1)) hx1
    simpa only [hrho0,hD0,sub_zero,_root_.zero_apply] using hh
  let z := actualInverseGraphFour N rho x
  have hznorm : ‖z‖ ≤ L*‖x‖ := by
    change ‖x+(-rho x) • N‖ ≤ _
    apply (norm_add_le _ _).trans
    rw [norm_smul,Real.norm_eq_abs,abs_neg,hN,mul_one]
    have hsq : ‖x‖^2 ≤ ‖x‖ := by nlinarith [norm_nonneg x]
    dsimp only [L]
    nlinarith [mul_le_mul_of_nonneg_left hsq hM]
  have hz : z ∈ actualFlatClosedUpperBallFour N r := by
    refine ⟨?_,hside⟩
    simp only [mem_closedBall,dist_zero_right]
    exact hznorm.trans ((mul_le_mul_of_nonneg_left hnormR hL.le).trans hRr)
  have hzinner : inner ℝ N z ≤ ‖z‖ := by
    simpa only [hN,one_mul] using real_inner_le_norm N z
  have hzz : actualGraphShearFour N rho z=x := (actual_inverse_graph_inverse_four hinv x).2
  have he := herr z hz
  rw [hzz] at he
  have herror : |u x-q*inner ℝ N z| ≤ (C*L*L^alpha)*‖x‖*‖x‖^alpha := by
    calc
      _ ≤ C*‖z‖^alpha*‖z‖ := he.trans (mul_le_mul_of_nonneg_left hzinner (by positivity))
      _ ≤ C*(L*‖x‖)^alpha*(L*‖x‖) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hznorm ha) hC)
          hznorm (norm_nonneg _) (by positivity)
      _ = _ := by rw [Real.mul_rpow hL.le (norm_nonneg x)]; ring
  have hzinnerEq : inner ℝ N z=inner ℝ N x-rho x := by
    change inner ℝ N (x+(-rho x) • N)=_
    rw [inner_add_right,inner_smul_right,real_inner_self_eq_norm_sq,hN,one_pow,mul_one]
    ring
  have hslope : |q*inner ℝ N z-q*inner ℝ N x| ≤ Q*M*‖x‖*‖x‖^alpha := by
    rw [hzinnerEq,show q*(inner ℝ N x-rho x)-q*inner ℝ N x= -q*rho x by ring,
      abs_mul,abs_neg]
    have hpower : ‖x‖ ≤ ‖x‖^alpha := Real.self_le_rpow_of_le_one (norm_nonneg _) hnorm1 ha1
    calc
      |q| * |rho x| ≤ Q*(M*‖x‖^2) := mul_le_mul hq hrhov (abs_nonneg _) hQ
      _ = (Q*M*‖x‖)*‖x‖ := by ring
      _ ≤ (Q*M*‖x‖)*‖x‖^alpha := mul_le_mul_of_nonneg_left hpower (by positivity)
  calc
    _ ≤ |u x-q*inner ℝ N z|+|q*inner ℝ N z-q*inner ℝ N x| :=
      abs_sub_le _ _ _
    _ ≤ (C*L*L^alpha)*‖x‖*‖x‖^alpha+Q*M*‖x‖*‖x‖^alpha := add_le_add herror hslope
    _ = _ := by dsimp only [K]; ring

end PowerConvexity
