import PowerConvexity.Analysis.ActualUniformGraphCoefficientBoundsFour
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap

/-! # Constructing the actual graph EllipticCoeff from the original operator

Both coercivity inequalities are proved for the actual inverse congruence.
The upper and lower constants use the same uniform graph derivative bound.
Measurability of the raw graph field is explicit, independently of any PDE
regularity or boundary Holder estimate.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
local notation "Mat" => Matrix (Fin (2+2)) (Fin (2+2)) ℝ
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

def actualUniformGraphEllipticCoeffFour {U V : Set E} (hV : IsOpen V)
    {N : E} (hN : ‖N‖=1) {rho : E → ℝ} {a : E → Mat}
    {lam Lambda D : ℝ} (hlam : 0 < lam) (hLamL : lam ≤ Lambda) (hD : 0 ≤ D)
    (hmap : MapsTo (actualGraphShearFour N rho) V U)
    (hnormal : ∀ x ∈ V, fderiv ℝ rho x N=0)
    (hderiv : ∀ x ∈ V, ‖fderiv ℝ rho x‖ ≤ D)
    (hMeasurable : ∀ i j, Measurable (fun x => actualGraphShearCoefficientFour N rho a x i j))
    (hcoercive : ∀ x ∈ U, ∀ v : E, lam*‖v‖^2 ≤ inner ℝ v (matMulE (a x) v))
    (hcoerciveInv : ∀ x ∈ U, ∀ v : E, Lambda⁻¹*‖v‖^2 ≤ inner ℝ v (matMulE (a x)⁻¹ v)) :
    EllipticCoeff (2+2) V where
  a := actualGraphShearCoefficientFour N rho a
  lam := lam/(1+D)^2
  Λ := Lambda*(1+D)^2
  measurable_comp := hMeasurable
  hlam := div_pos hlam (sq_pos_of_pos (by positivity))
  hΛ := by
    have hsq : 1 ≤ (1+D)^2 := by nlinarith
    exact (div_le_self hlam.le hsq).trans
      (hLamL.trans (le_mul_of_one_le_right (hlam.le.trans hLamL) hsq))
  coercive := by
    filter_upwards [ae_restrict_mem hV.measurableSet] with x hx
    let G := actualShearLinearEquivFour N (fderiv ℝ rho x) (hnormal x hx)
    have hG : ‖G.toContinuousLinearMap‖ ≤ 1+D :=
      (actual_shear_linear_norm_bound_four N _ (hnormal x hx)).trans
        (by rw [hN,mul_one]; linarith [hderiv x hx])
    intro v
    rw [actual_graph_shear_coefficient_congruence_four a (hnormal x hx)]
    exact actual_linear_congruence_coercive_two G _ hlam.le (by positivity) hG
      (hcoercive _ (hmap hx)) v
  coercive_inv := by
    filter_upwards [ae_restrict_mem hV.measurableSet] with x hx
    let G := actualShearLinearEquivFour N (fderiv ℝ rho x) (hnormal x hx)
    have hG : ‖G.symm.toContinuousLinearMap‖ ≤ 1+D :=
      (actual_shear_inverse_norm_bound_four N _ (hnormal x hx)).trans
        (by rw [hN,mul_one]; linarith [hderiv x hx])
    intro v
    rw [actual_graph_shear_coefficient_congruence_four a (hnormal x hx)]
    exact actual_linear_congruence_inverse_coercive_two G _ (hlam.trans_le hLamL)
      (by positivity) hG (hcoerciveInv _ (hmap hx)) v

theorem actual_graph_coefficient_measurable_four {N : E} {rho : E → ℝ} {a : E → Mat}
    (hrho : Measurable rho) (hderiv : Measurable (fderiv ℝ rho))
    (ha : ∀ i j, Measurable (fun x => a x i j)) :
    ∀ i j, Measurable (fun x => actualGraphShearCoefficientFour N rho a x i j) := by
  have hPhi : Measurable (actualGraphShearFour N rho) :=
    measurable_id.add (hrho.smul measurable_const)
  have hQ (k l : Fin (2+2)) : Measurable
      (fun x => actualShearInverseMatrixFour N (fderiv ℝ rho x) k l) :=
    measurable_const.sub (measurable_const.mul (hderiv.apply_continuousLinearMap (EuclideanSpace.single l 1)))
  intro i j
  simp only [actualGraphShearCoefficientFour,Matrix.mul_apply,Matrix.transpose_apply]
  apply Finset.measurable_sum _
  intro k _
  apply Measurable.mul _ (hQ j k)
  apply Finset.measurable_sum _
  intro l _
  exact (hQ i l).mul ((ha l k).comp hPhi)

def actualUniformLocalGraphEllipticCoeffFour {U V W : Set E}
    (hV : IsOpen V) (hW : MeasurableSet W) (hVW : V ⊆ W)
    {N : E} (hN : ‖N‖=1) {rho : E → ℝ} {a : E → Mat}
    {lam Lambda D : ℝ} (hlam : 0 < lam) (hLamL : lam ≤ Lambda) (hD : 0 ≤ D)
    (hmap : MapsTo (actualGraphShearFour N rho) V U)
    (hnormal : ∀ x ∈ V, fderiv ℝ rho x N=0)
    (hderiv : ∀ x ∈ V, ‖fderiv ℝ rho x‖ ≤ D)
    (hContinuous : ∀ i j, ContinuousOn
      (fun x => actualGraphShearCoefficientFour N rho a x i j) W)
    (hcoercive : ∀ x ∈ U, ∀ v : E, lam*‖v‖^2 ≤ inner ℝ v (matMulE (a x) v))
    (hcoerciveInv : ∀ x ∈ U, ∀ v : E, Lambda⁻¹*‖v‖^2 ≤ inner ℝ v (matMulE (a x)⁻¹ v)) :
    EllipticCoeff (2+2) V := by
  classical
  let B : E → Mat := W.piecewise (actualGraphShearCoefficientFour N rho a) (fun _ => 1)
  have hB (x : E) (hx : x ∈ W) : B x=actualGraphShearCoefficientFour N rho a x := by
    simp only [B,Set.piecewise,if_pos hx]
  refine {
    a := B
    lam := lam/(1+D)^2
    Λ := Lambda*(1+D)^2
    measurable_comp := ?_
    hlam := div_pos hlam (sq_pos_of_pos (by positivity))
    hΛ := ?_
    coercive := ?_
    coercive_inv := ?_
  }
  · intro i j
    have hh := (hContinuous i j).measurable_piecewise
      (g := fun _ : E => (1 : Mat) i j) continuousOn_const hW
    have he : (fun x => B x i j)=W.piecewise
        (fun x => actualGraphShearCoefficientFour N rho a x i j) (fun _ => (1 : Mat) i j) := by
      funext x
      by_cases hx : x∈W <;> simp [B,Set.piecewise,hx]
    rw [he]
    exact hh
  · have hsq : 1 ≤ (1+D)^2 := by nlinarith
    exact (div_le_self hlam.le hsq).trans
      (hLamL.trans (le_mul_of_one_le_right (hlam.le.trans hLamL) hsq))
  · filter_upwards [ae_restrict_mem hV.measurableSet] with x hx
    let G := actualShearLinearEquivFour N (fderiv ℝ rho x) (hnormal x hx)
    have hG : ‖G.toContinuousLinearMap‖ ≤ 1+D :=
      (actual_shear_linear_norm_bound_four N _ (hnormal x hx)).trans
        (by rw [hN,mul_one]; linarith [hderiv x hx])
    intro v
    rw [hB x (hVW hx),actual_graph_shear_coefficient_congruence_four a (hnormal x hx)]
    exact actual_linear_congruence_coercive_two G _ hlam.le (by positivity) hG
      (hcoercive _ (hmap hx)) v
  · filter_upwards [ae_restrict_mem hV.measurableSet] with x hx
    let G := actualShearLinearEquivFour N (fderiv ℝ rho x) (hnormal x hx)
    have hG : ‖G.symm.toContinuousLinearMap‖ ≤ 1+D :=
      (actual_shear_inverse_norm_bound_four N _ (hnormal x hx)).trans
        (by rw [hN,mul_one]; linarith [hderiv x hx])
    intro v
    rw [hB x (hVW hx),actual_graph_shear_coefficient_congruence_four a (hnormal x hx)]
    exact actual_linear_congruence_inverse_coercive_two G _ (hlam.trans_le hLamL)
      (by positivity) hG (hcoerciveInv _ (hmap hx)) v

theorem actual_uniform_local_graph_coefficient_agrees_four {U V W : Set E}
    (hV : IsOpen V) (hW : MeasurableSet W) (hVW : V ⊆ W)
    {N : E} (hN : ‖N‖=1) {rho : E → ℝ} {a : E → Mat}
    {lam Lambda D : ℝ} (hlam : 0 < lam) (hLamL : lam ≤ Lambda) (hD : 0 ≤ D)
    (hmap : MapsTo (actualGraphShearFour N rho) V U)
    (hnormal : ∀ x ∈ V, fderiv ℝ rho x N=0)
    (hderiv : ∀ x ∈ V, ‖fderiv ℝ rho x‖ ≤ D)
    (hContinuous : ∀ i j, ContinuousOn
      (fun x => actualGraphShearCoefficientFour N rho a x i j) W)
    (hcoercive : ∀ x ∈ U, ∀ v : E, lam*‖v‖^2 ≤ inner ℝ v (matMulE (a x) v))
    (hcoerciveInv : ∀ x ∈ U, ∀ v : E, Lambda⁻¹*‖v‖^2 ≤ inner ℝ v (matMulE (a x)⁻¹ v)) :
    EqOn (actualUniformLocalGraphEllipticCoeffFour hV hW hVW hN hlam hLamL hD
      hmap hnormal hderiv hContinuous hcoercive hcoerciveInv).a
        (actualGraphShearCoefficientFour N rho a) W := by
  classical
  intro x hx
  exact piecewise_eq_of_mem W (actualGraphShearCoefficientFour N rho a) (fun _ => 1) hx

end PowerConvexity
