import PowerConvexity.Analysis.ActualUniformGraphQuotientInputFour
import PowerConvexity.Analysis.ActualUniformPhysicalZeroQuotientFour

/-! # Uniform actual boundary quotient in genuine graph charts

Uniform ellipticity, the original bounded response and load, and common C2
graph bounds determine the radius and power estimate before the graph and
response. The original zero boundary value gives the true flat zero trace.
No Holder bound for the coefficients is assumed.
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

theorem actual_uniform_graph_zero_boundary_quotient_four
    {lam Lambda D₀ A₀ H₀ F M : ℝ} (hlam : 0 < lam) (hLambda : lam ≤ Lambda)
    (hD₀ : 0 ≤ D₀) (hA₀ : 0 ≤ A₀) (hH₀ : 0 ≤ H₀) (hF : 0 ≤ F) (hM : 0 ≤ M) :
    ∃ R > 0, R ≤ (1/2 : ℝ) ∧ ∃ alpha : ℝ, 0 < alpha ∧ alpha < 1 ∧ ∃ C > 0,
      ∀ N : E, ‖N‖=1 → ∀ U : Set E, IsOpen U →
      ∀ (rho u f : E → ℝ) (a : E → Mat),
      (∀ x ∈ closedBall (0 : E) 2, ContDiffAt ℝ 3 rho x) →
      (∀ x : E, ∀ t : ℝ, rho (x+t • N)=rho x) →
      (∀ x ∈ closedBall (0 : E) 2,
        actualGraphShearFour N rho x ∈ U ↔ 0 < inner ℝ N x) →
      (∀ x ∈ U, (a x).PosDef) →
      (∀ i j, ContDiffOn ℝ 1 (fun x => a x i j) U) →
      (∀ x ∈ U, ∀ j,
        (∑ i, fderiv ℝ (fun y => a y i j) x (EuclideanSpace.single i 1))=0) →
      (∀ x ∈ actualFlatUpperBallFour N 1,
        ‖actualMatrixOperatorTwo (a (actualGraphShearFour N rho x))‖ ≤ A₀) →
      (∀ x ∈ actualFlatUpperBallFour N 1, ‖fderiv ℝ rho x‖ ≤ D₀) →
      (∀ x ∈ actualFlatUpperBallFour N 1, ‖realHessian rho x‖ ≤ H₀) →
      (∀ x ∈ U, ∀ v : E, lam*‖v‖^2 ≤ inner ℝ v (matMulE (a x) v)) →
      (∀ x ∈ U, ∀ v : E, Lambda⁻¹*‖v‖^2 ≤ inner ℝ v (matMulE (a x)⁻¹ v)) →
      ContinuousOn f U → (∀ x ∈ U, |f x| ≤ F) →
      ContDiffOn ℝ 2 u U → ContinuousOn u (closure U) →
      (∀ x ∈ frontier U, u x=0) → (∀ x ∈ closure U, |u x| ≤ M) →
      (∀ x ∈ U, (∑ i, ∑ j, a x i j*euclideanHessian u x i j) = -f x) →
      ∃ q : ℝ, |q| ≤ C ∧ ∀ x ∈ actualFlatClosedUpperBallFour N R,
        |u (actualGraphShearFour N rho x)-q*inner ℝ N x| ≤ C*‖x‖^alpha*inner ℝ N x := by
  let ell := lam/(1+D₀)^2
  let cap := Lambda*(1+D₀)^2
  have hell : 0 < ell := div_pos hlam (sq_pos_of_pos (by positivity))
  have hsq : 1 ≤ (1+D₀)^2 := by nlinarith
  have hcap : ell ≤ cap :=
    (div_le_self hlam.le hsq).trans
      (hLambda.trans (le_mul_of_one_le_right (hlam.le.trans hLambda) hsq))
  obtain ⟨R,hR,hR2,alpha,ha,ha1,C,hC,hquot⟩ :=
    actual_uniform_physical_zero_boundary_quotient_four
      ((one_le_div hell).mpr hcap)
      (show 0 ≤ (16*A₀*H₀)/ell by positivity)
      (show 0 ≤ F/ell by positivity) hM
  refine ⟨R,hR,hR2,alpha,ha,ha1,C,hC,?_⟩
  intro N hN U hU rho u f a hrho hinv hmap hpos hreg hdiv haB hDB hHB hcoerc hcoercInv
    hf hfB hu huC hzero hub heq
  let V := actualFlatUpperBallFour N 1
  have hV : IsOpen V := actualFlatUpperBallFour_isOpen N 1
  have hV2 : V ⊆ closedBall (0 : E) 2 := fun x hx =>
    closedBall_subset_closedBall (by norm_num) (ball_subset_closedBall hx.1)
  have hPhi : MapsTo (actualGraphShearFour N rho) V U :=
    fun x hx => (hmap x (hV2 hx)).mpr hx.2
  have hRho2 : ContDiffOn ℝ 2 rho V := fun x hx =>
    ((hrho x (hV2 hx)).of_le (by norm_num)).contDiffWithinAt
  have hRawC : ∀ i j, ContinuousOn (fun x => actualGraphShearCoefficientFour N rho a x i j) V :=
    fun i j => (actual_graph_shear_coefficient_regular_four hV hRho2 hreg hPhi i j).continuousOn
  have hnormal : ∀ x ∈ V, fderiv ℝ rho x N=0 :=
    fun x _ => actual_graph_normal_invariance_fderiv_four hinv x
  let A := actualUniformLocalGraphEllipticCoeffFour hV hV.measurableSet (Subset.rfl)
    hN hlam hLambda hD₀ hPhi hnormal hDB hRawC hcoerc hcoercInv
  have hcoeff : EqOn A.a (actualGraphShearCoefficientFour N rho a) V :=
    actual_uniform_local_graph_coefficient_agrees_four hV hV.measurableSet (Subset.rfl)
      hN hlam hLambda hD₀ hPhi hnormal hDB hRawC hcoerc hcoercInv
  let Q := actualUniformGraphQuotientInputFour hU hN hA₀ hH₀ A hcoeff hrho hinv hmap
    hpos hreg hdiv haB hHB hf hfB hu huC heq
  have hQzero : ∀ x ∈ closedBall (0 : E) 1, inner ℝ N x=0 → Q.solution x=0 := by
    have hh := actual_graph_zero_boundary_transport_four hU (x := (0 : E)) hN
      (by norm_num : (0 : ℝ) < 2)
      (fun x hx => (hrho x (ball_subset_closedBall hx)).continuousAt)
      (by simpa only [zero_add] using hmap) hzero
    intro x hx ht
    change u (actualGraphShearFour N rho x)=0
    simpa only [zero_add] using hh x
      (by simpa only [show (2 : ℝ)/2=1 by norm_num] using hx) ht
  have hQC := actual_graph_closed_halfball_maps_closure_four hU hN
    (fun x hx => (hrho x hx).continuousAt) hmap
  have hQB : ∀ x ∈ actualFlatClosedUpperBallFour N 1, |Q.solution x| ≤ M :=
    fun x hx => hub _ (hQC hx)
  exact hquot N hN Q hQzero hQB

end PowerConvexity
