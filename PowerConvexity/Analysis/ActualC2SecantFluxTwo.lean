import PowerConvexity.Analysis.ActualC2DeterminantSecantTwo

/-! # The actual determinant secant as a distributional flux identity

This version requires no auxiliary elliptic-coefficient bundle.  It can be
applied directly to translated C2 potentials before passing to a derivative.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators Matrix.Norms.Elementwise
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] atjInstance1 atjInstance2 atjInstance3 atjInstance4 atjInstance5 atjInstance6

theorem actual_hasWeakDiv_congr_on_two
    {U : Set E} (hU : IsOpen U) {F G : E → E} {f g : E → ℝ}
    (hdiv : HasWeakDiv f F U) (hFG : EqOn F G U) (hfg : EqOn f g U) :
    HasWeakDiv g G U := by
  intro phi hp hc hs
  have h := hdiv phi hp hc hs
  have hL : (∫ x in U, ∑ i, F x i*fderiv ℝ phi x (EuclideanSpace.single i 1))=
      ∫ x in U, ∑ i, G x i*fderiv ℝ phi x (EuclideanSpace.single i 1) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    rw [hFG hx]
  have hR : (∫ x in U, f x*phi x)=∫ x in U, g x*phi x := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    rw [hfg hx]
  rwa [hL,hR] at h

theorem actual_hasWeakDiv_const_smul_two
    {U : Set E} {F : E → E} {f : E → ℝ}
    (hdiv : HasWeakDiv f F U) (k : ℝ) :
    HasWeakDiv (fun x => k*f x) (fun x => k • F x) U := by
  intro phi hp hc hs
  have h := hdiv phi hp hc hs
  change (∫ x in U, ∑ i, k*F x i*fderiv ℝ phi x (EuclideanSpace.single i 1))=
    -∫ x in U, (k*f x)*phi x
  simp only [mul_assoc,← Finset.mul_sum]
  rw [integral_const_mul,integral_const_mul,h]
  ring

theorem actual_C2_midpoint_secant_hasWeakDiv_two
    {V : Set E} (hV : IsOpen V) {u v : E → ℝ}
    (hu : ContDiffOn ℝ 2 u V) (hv : ContDiffOn ℝ 2 v V)
    {c : E} {r : ℝ} (hclosed : closedBall c r ⊆ V) :
    HasWeakDiv
      (fun x => (complexHessian realDirections imagDirections v x).det.re-
        (complexHessian realDirections imagDirections u x).det.re)
      (fun x => matMulE (complexCofactorCoeff (fun y => (1/2 : ℝ)*(u y+v y)) x)
        (smoothGradField (fun y => v y-u y) x)) (ball c r) := by
  let m : E → ℝ := fun y => (1/2 : ℝ)*(u y+v y)
  have hm : ContDiffOn ℝ 2 m V := contDiffOn_const.mul (hu.add hv)
  have hc := actual_C2_cofactor_continuousOn_two hV hm
  have hAc (i j : Fin (2+2)) : ContinuousOn (fun x => complexCofactorCoeff m x i j)
      (closedBall c r) :=
    (continuousOn_pi.mp (continuousOn_pi.mp hc i) j).mono hclosed
  have hdiv (j : Fin (2+2)) : HasWeakDiv (fun _ => 0)
      (fun x => WithLp.toLp 2 (fun i => complexCofactorCoeff m x i j)) (ball c r) :=
    actual_C2_cofactor_column_hasWeakDiv_zero_two isOpen_ball
      (hm.mono (ball_subset_closedBall.trans hclosed)) j
  have hh := actual_C2_gradient_flux_hasWeakDiv_two hV hclosed hAc hdiv (hv.sub hu)
  apply actual_hasWeakDiv_congr_on_two isOpen_ball hh (fun _ _ => rfl)
  intro x hx
  exact actual_C2_midpoint_cofactor_secant_contraction_two
    (hu.contDiffAt (hV.mem_nhds (hclosed (ball_subset_closedBall hx))))
    (hv.contDiffAt (hV.mem_nhds (hclosed (ball_subset_closedBall hx))))

theorem actual_C2_midpoint_difference_quotient_hasWeakDiv_two
    {V : Set E} (hV : IsOpen V) {u v : E → ℝ}
    (hu : ContDiffOn ℝ 2 u V) (hv : ContDiffOn ℝ 2 v V)
    {c : E} {r : ℝ} (hclosed : closedBall c r ⊆ V) (h : ℝ) :
    HasWeakDiv
      (fun x => h⁻¹*((complexHessian realDirections imagDirections v x).det.re-
        (complexHessian realDirections imagDirections u x).det.re))
      (fun x => h⁻¹ • matMulE (complexCofactorCoeff (fun y => (1/2 : ℝ)*(u y+v y)) x)
        (smoothGradField (fun y => v y-u y) x)) (ball c r) := by
  exact actual_hasWeakDiv_const_smul_two
    (actual_C2_midpoint_secant_hasWeakDiv_two hV hu hv hclosed) h⁻¹

end PowerConvexity
