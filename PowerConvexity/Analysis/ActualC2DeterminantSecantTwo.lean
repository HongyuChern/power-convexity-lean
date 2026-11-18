import PowerConvexity.Analysis.ActualC2DistributionalFluxTwo
import PowerConvexity.Calculus.ActualHolderCofactorPairingTwo
import CHS.Calculus.HessianOrder

/-! # Exact weak linearization between two actual C2 potentials

For a 2 by 2 determinant the secant is contraction with the cofactor of
the midpoint Hessian.  The actual midpoint potential is still C2, so its
cofactor columns have zero distributional divergence.  The resulting weak
equation is valid on every H01 test without assuming either potential C3.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators Matrix.Norms.Elementwise
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
local notation "Mat" => Matrix (Fin 2) (Fin 2) ℂ
attribute [local instance] atjInstance1 atjInstance2 atjInstance3 atjInstance4 atjInstance5 atjInstance6

theorem actual_complex_determinant_midpoint_secant_two (A B : Mat) :
    (∑ i : Fin 2, ∑ j : Fin 2,
      ((1/2 : ℝ) • (A+B)).adjugate j i*(B-A) i j)=B.det-A.det := by
  simp only [Fin.sum_univ_two,Matrix.adjugate_fin_two,Matrix.det_fin_two,
    Matrix.smul_apply,Matrix.add_apply,Matrix.sub_apply,Matrix.of_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
    Complex.real_smul,smul_eq_mul,Complex.ofReal_div,Complex.ofReal_one,
    Complex.ofReal_ofNat]
  ring

theorem actual_complex_hessian_sub_two
    {u v : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x) :
    complexHessian realDirections imagDirections (fun y => v y-u y) x=
      complexHessian realDirections imagDirections v x-
      complexHessian realDirections imagDirections u x := by
  have he : (fun y => v y-u y)=(fun y => v y+(-1 : ℝ)*u y) := by funext y; ring
  rw [he,complexHessian_add hv (contDiffAt_const.mul hu),complexHessian_const_mul]
  simp only [neg_smul,one_smul,sub_eq_add_neg]

theorem actual_C2_midpoint_cofactor_secant_contraction_two
    {u v : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x) :
    (∑ i, ∑ j, complexCofactorCoeff (fun y => (1/2 : ℝ)*(u y+v y)) x i j*
      euclideanHessian (fun y => v y-u y) x i j)=
      (complexHessian realDirections imagDirections v x).det.re-
      (complexHessian realDirections imagDirections u x).det.re := by
  rw [← actual_complex_cofactor_hessian_contraction_two (hv.sub hu),
    complexHessian_const_mul,complexHessian_add hu hv,
    actual_complex_hessian_sub_two hu hv,actual_complex_determinant_midpoint_secant_two,
    Complex.sub_re]

theorem actual_C2_scaled_midpoint_secant_weak_equation_two
    {V : Set E} (hV : IsOpen V) {u v : E → ℝ}
    (hu : ContDiffOn ℝ 2 u V) (hv : ContDiffOn ℝ 2 v V)
    {c : E} {r k : ℝ} (hclosed : closedBall c r ⊆ V)
    (A : EllipticCoeff (2+2) (ball c r))
    (ha : ∀ x ∈ V, A.a x=k • complexCofactorCoeff (fun y => (1/2 : ℝ)*(u y+v y)) x) :
    ActualScalarWeakEquationTwo A
      (fun x => k*((complexHessian realDirections imagDirections u x).det.re-
        (complexHessian realDirections imagDirections v x).det.re))
      (fun x => v x-u x) := by
  let m : E → ℝ := fun y => (1/2 : ℝ)*(u y+v y)
  have hm : ContDiffOn ℝ 2 m V := contDiffOn_const.mul (hu.add hv)
  have hc := actual_C2_cofactor_continuousOn_two hV hm
  have hAc (i j : Fin (2+2)) : ContinuousOn (fun x => A.a x i j) (closedBall c r) := by
    apply (((continuousOn_pi.mp (continuousOn_pi.mp hc i) j).const_mul k).mono hclosed).congr
    intro x hx
    exact congrArg (fun M : Matrix (Fin (2+2)) (Fin (2+2)) ℝ => M i j) (ha x (hclosed hx))
  have hd (j : Fin (2+2)) : HasWeakDiv (fun _ => 0)
      (fun x => WithLp.toLp 2 (fun i => A.a x i j)) (ball c r) := by
    have hbase := actual_C2_cofactor_column_hasWeakDiv_zero_two isOpen_ball
      (hm.mono (ball_subset_closedBall.trans hclosed)) j
    apply actual_hasWeakDiv_zero_congr_on_two isOpen_ball
      (actual_hasWeakDiv_zero_const_smul_two hbase k)
    intro x hx
    ext i
    exact (congrArg (fun M : Matrix (Fin (2+2)) (Fin (2+2)) ℝ => M i j)
      (ha x (hclosed (ball_subset_closedBall hx)))).symm
  have hweak := actual_C2_distributional_scalar_equation_two hV hclosed A hAc hd (hv.sub hu)
  apply actual_scalar_weak_source_congr_ae_two (hu := hweak)
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  have hxV := hclosed (ball_subset_closedBall hx)
  have hpair := actual_C2_midpoint_cofactor_secant_contraction_two
    (hu.contDiffAt (hV.mem_nhds hxV)) (hv.contDiffAt (hV.mem_nhds hxV))
  change -(∑ i, ∑ j, A.a x i j*euclideanHessian (fun y => v y-u y) x i j)=_
  have he (i j : Fin (2+2)) : A.a x i j=
      k*complexCofactorCoeff (fun y => (1/2 : ℝ)*(u y+v y)) x i j :=
    congrArg (fun M : Matrix (Fin (2+2)) (Fin (2+2)) ℝ => M i j) (ha x hxV)
  simp only [he,mul_assoc,← Finset.mul_sum]
  rw [hpair]
  ring

theorem actual_C2_scaled_midpoint_difference_quotient_weak_two
    {V : Set E} (hV : IsOpen V) {u v : E → ℝ}
    (hu : ContDiffOn ℝ 2 u V) (hv : ContDiffOn ℝ 2 v V)
    {c : E} {r k : ℝ} (hclosed : closedBall c r ⊆ V)
    (A : EllipticCoeff (2+2) (ball c r))
    (ha : ∀ x ∈ V, A.a x=k • complexCofactorCoeff (fun y => (1/2 : ℝ)*(u y+v y)) x)
    (h : ℝ) :
    ActualScalarWeakEquationTwo A
      (fun x => h⁻¹*(k*((complexHessian realDirections imagDirections u x).det.re-
        (complexHessian realDirections imagDirections v x).det.re)))
      (fun x => h⁻¹*(v x-u x)) := by
  exact actual_scalar_weak_smul_two isOpen_ball
    (actual_C2_scaled_midpoint_secant_weak_equation_two hV hu hv hclosed A ha) h⁻¹

end PowerConvexity
