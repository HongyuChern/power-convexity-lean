import PowerConvexity.Analysis.ActualCommonGraphHolderBoundsFour
import PowerConvexity.Analysis.ActualUniformGraphEllipticCoeffFour

/-! # Genuine common physical drift input from the normalized original PDE

All constants are explicit functions of the original common bounds. The
coefficient is the true inverse graph congruence with a measurable extension;
the solution, load, drift and flat zero trace are the actual transported ones.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
local notation "Mat" => Matrix (Fin (2+2)) (Fin (2+2)) ℝ
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

def actualCommonDomainGraphPhysicalInputFour
    {U : Set E} (hU : IsOpen U) {lam Lambda alpha Ka Kf B D₀ H₀ Kd Kh : ℝ}
    (hlam : 0 < lam) (halpha : 0 < alpha) (halpha1 : alpha ≤ 1)
    (hKa : 0 ≤ Ka) (hKf : 0 ≤ Kf) (hD₀ : 0 ≤ D₀) (hH₀ : 0 ≤ H₀)
    (hKd : 0 ≤ Kd) (hKh : 0 ≤ Kh)
    (D : ActualContinuousDomainLinearDataFour U lam Lambda alpha Ka Kf)
    {N : E} (hN : ‖N‖=1) {rho : E → ℝ}
    (hrho : ∀ x ∈ closedBall (0 : E) 2, ContDiffAt ℝ 3 rho x)
    (hrho0 : rho 0=0) (hD0 : fderiv ℝ rho 0=0) (hfrozen : D.coeff.a 0=1)
    (hinv : ∀ x : E, ∀ t : ℝ, rho (x+t • N)=rho x)
    (hmap : ∀ x ∈ closedBall (0 : E) 2,
      actualGraphShearFour N rho x ∈ U ↔ 0 < inner ℝ N x)
    (hDB : ∀ x ∈ closedBall (0 : E) 1, ‖fderiv ℝ rho x‖ ≤ D₀)
    (hHB : ∀ x ∈ closedBall (0 : E) 1, ‖realHessian rho x‖ ≤ H₀)
    (hDLip : ∀ x ∈ closedBall (0 : E) 1, ∀ y ∈ closedBall (0 : E) 1,
      ‖fderiv ℝ rho x-fderiv ℝ rho y‖ ≤ Kd*‖x-y‖)
    (hHLip : ∀ x ∈ closedBall (0 : E) 1, ∀ y ∈ closedBall (0 : E) 1,
      ‖realHessian rho x-realHessian rho y‖ ≤ Kh*‖x-y‖)
    (hzero : ∀ x ∈ frontier U, D.solution x=0)
    (hbound : ∀ x ∈ closure U, |D.solution x| ≤ B) :
    let L := 1+D₀
    let A₀ := 1+Ka*L^alpha
    ActualFlatDriftPhysicalInputFour N (lam/L^2) (Lambda*L^2) alpha
      (2*L*A₀*(2*Kd)+L^2*(Ka*L^alpha))
      (16*((Ka*L^alpha)*H₀+A₀*(2*Kh)))
      (Kf*L^alpha) (16*A₀*H₀) B := by
  let V := actualFlatUpperBallFour N 1
  let W := actualFlatClosedUpperBallFour N 1
  let L := 1+D₀
  let A₀ := 1+Ka*L^alpha
  have hL : 0 < L := by dsimp [L]; positivity
  have hA₀ : 0 ≤ A₀ := by dsimp [A₀]; positivity
  have hV : IsOpen V := actualFlatUpperBallFour_isOpen N 1
  have hVW : V ⊆ W := fun x hx => ⟨ball_subset_closedBall hx.1,(show 0 < inner ℝ N x from hx.2).le⟩
  have hW2 : W ⊆ closedBall (0 : E) 2 :=
    fun x hx => closedBall_subset_closedBall (by norm_num) hx.1
  have hreg1 (x : E) (hx : x ∈ closedBall (0 : E) 1) : ContDiffAt ℝ 3 rho x :=
    hrho x (closedBall_subset_closedBall (by norm_num) hx)
  have hPhi : MapsTo (actualGraphShearFour N rho) V U :=
    fun x hx => (hmap x (hW2 (hVW hx))).mpr hx.2
  have hPhiC : MapsTo (actualGraphShearFour N rho) W (closure U) :=
    actual_graph_closed_halfball_maps_closure_four hU hN
      (fun x hx => (hrho x hx).continuousAt) hmap
  have haC := actual_holder_matrix_entries_continuous_four halpha D.holder
  have hfC := actual_holder_scalar_continuous_four halpha D.source_holder
  have hPhiCont : ContinuousOn (actualGraphShearFour N rho) W :=
    fun x hx => (actual_graph_shear_contDiffAt_four (hrho x (hW2 hx))).continuousAt.continuousWithinAt
  have hDCont : ContinuousOn (fderiv ℝ rho) W := fun x hx =>
    ((hrho x (hW2 hx)).fderiv_right (m := 2) (by norm_num)).continuousAt.continuousWithinAt
  have hRawC : ∀ i j, ContinuousOn
      (fun x => actualGraphShearCoefficientFour N rho D.coeff.a x i j) W := by
    intro i j
    simp only [actualGraphShearCoefficientFour,Matrix.mul_apply,Matrix.transpose_apply]
    have hQ (k l : Fin (2+2)) : ContinuousOn
        (fun x => actualShearInverseMatrixFour N (fderiv ℝ rho x) k l) W :=
      continuousOn_const.sub (continuousOn_const.mul (hDCont.clm_apply continuousOn_const))
    apply continuousOn_finsetSum _
    intro k _
    apply ContinuousOn.mul _ (hQ j k)
    apply continuousOn_finsetSum _
    intro l _
    exact (hQ i l).mul ((haC l k).comp hPhiCont hPhiC)
  have hcoerc0 := actual_elliptic_bounds_pointwise_two hU D.coeff
    (fun i j => (haC i j).mono subset_closure)
  have hcoerc : ∀ x ∈ U, ∀ v : E, lam*‖v‖^2 ≤ inner ℝ v (matMulE (D.coeff.a x) v) := by
    intro x hx v
    exact (mul_le_mul_of_nonneg_right D.lower (sq_nonneg _)).trans (hcoerc0 x hx v).1
  have hInv0 := actual_holder_elliptic_inverse_coercivity_pointwise_four hU D.coeff
    (fun i j => (haC i j).mono subset_closure) D.positive
  have hInvLe : Lambda⁻¹ ≤ D.coeff.Λ⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le D.coeff.Λ_pos D.upper
  have hInv : ∀ x ∈ U, ∀ v : E,
      Lambda⁻¹*‖v‖^2 ≤ inner ℝ v (matMulE (D.coeff.a x)⁻¹ v) := by
    intro x hx v
    exact (mul_le_mul_of_nonneg_right hInvLe (sq_nonneg _)).trans (hInv0 x hx v)
  have hLam : lam ≤ Lambda := D.lower.trans (D.coeff.hΛ.trans D.upper)
  have hnormal : ∀ x ∈ V, fderiv ℝ rho x N=0 :=
    fun x _ => actual_graph_normal_invariance_fderiv_four hinv x
  let A := actualUniformLocalGraphEllipticCoeffFour hV
    (isClosed_closedBall.inter (isClosed_le continuous_const (by fun_prop))).measurableSet
    hVW hN hlam hLam hD₀ hPhi hnormal (fun x hx => hDB x (hVW hx).1) hRawC hcoerc hInv
  have hcoeff : EqOn A.a (actualGraphShearCoefficientFour N rho D.coeff.a) W :=
    actual_uniform_local_graph_coefficient_agrees_four hV
      (isClosed_closedBall.inter (isClosed_le continuous_const (by fun_prop))).measurableSet
      hVW hN hlam hLam hD₀ hPhi hnormal (fun x hx => hDB x (hVW hx).1) hRawC hcoerc hInv
  have hLip := actual_unit_graph_lipschitz_four hN
    (fun x hx => (hreg1 x hx).differentiableAt (by norm_num)) hDB
  have haBound : ∀ x ∈ W,
      ‖actualMatrixOperatorTwo (D.coeff.a (actualGraphShearFour N rho x))‖ ≤ A₀ :=
    actual_unit_graph_frozen_operator_bound_four hKa hD₀ halpha.le hrho0 hfrozen hPhiC hLip D.holder
  have haHolder : ∀ x ∈ W, ∀ y ∈ W,
      ‖actualMatrixOperatorTwo (D.coeff.a (actualGraphShearFour N rho x))-
        actualMatrixOperatorTwo (D.coeff.a (actualGraphShearFour N rho y))‖ ≤
          (Ka*L^alpha)*‖x-y‖^alpha :=
    actual_holder_lipschitz_pullback_four hKa hL.le halpha.le hPhiC
      (fun x hx y hy => hLip x hx.1 y hy.1) D.holder
  have hfHolder : ∀ x ∈ W, ∀ y ∈ W,
      |D.source (actualGraphShearFour N rho x)-D.source (actualGraphShearFour N rho y)| ≤
        (Kf*L^alpha)*‖x-y‖^alpha := by
    have hh := actual_holder_lipschitz_pullback_four hKf hL.le halpha.le hPhiC
      (fun x hx y hy => hLip x hx.1 y hy.1)
      (show ∀ x ∈ closure U, ∀ y ∈ closure U, ‖D.source x-D.source y‖ ≤ Kf*‖x-y‖^alpha by
        simpa only [Real.norm_eq_abs] using D.source_holder)
    simpa only [Real.norm_eq_abs] using hh
  have hDHolder := actual_unit_ball_lipschitz_holder_four hKd halpha.le halpha1 hDLip
  have hHHolder := actual_unit_ball_lipschitz_holder_four (Z := E →L[ℝ] E →L[ℝ] ℝ)
    (g := realHessian rho) hKh halpha.le halpha1 hHLip
  exact actualUniformGraphPhysicalInputFour hU hN hA₀ hD₀ hH₀
    (by positivity : 0 ≤ Ka*L^alpha) (by positivity : 0 ≤ 2*Kd) (by positivity : 0 ≤ 2*Kh)
    A hcoeff hrho hrho0 hD0 hfrozen hinv hmap D.positive D.regular haC D.divergence
    haBound (fun x hx => hDB x hx.1) (fun x hx => hHB x hx.1) haHolder
    (fun x hx y hy => hDHolder x hx.1 y hy.1) (fun x hx y hy => hHHolder x hx.1 y hy.1)
    hfC hfHolder D.solution_regular D.solution_continuous hzero hbound D.equation

end PowerConvexity
