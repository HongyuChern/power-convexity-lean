import PowerConvexity.Analysis.ActualC1LinearWeakDerivativeTwo
import PowerConvexity.Analysis.ActualCofactorSecondVariationTwo

/-! # The genuine second cofactor weak variation from only C3 regularity

The first variation is classical at C3.  Its directional derivative is
taken in the actual weak formulation, with the cofactor derivative retained
as the exact quadratic third-jet source.  No fourth derivative is assumed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators ComplexOrder Matrix.Norms.Elementwise
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
local notation "Mat" => Matrix (Fin (2+2)) (Fin (2+2)) ℝ
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul
attribute [local instance] ahdTripleNormedGroup ahdTripleNormedSpace ahdTripleModule ahdTripleTopology

theorem actual_C3_scaled_cofactor_C1_two
    {U : Set E} (hU : IsOpen U) {u : E → ℝ} (hu : ContDiffOn ℝ 3 u U)
    {a : E → Mat} {c : ℝ} (ha : ∀ y ∈ U, a y=c⁻¹ • complexCofactorCoeff u y) :
    ∀ i j, ContDiffOn ℝ 1 (fun y => a y i j) U := by
  have hH : ContDiffOn ℝ 1 (realHessian u) U :=
    (hu.fderiv_of_isOpen hU (m := 2) (by norm_num)).fderiv_of_isOpen hU (m := 1) (by norm_num)
  have hF : ContDiff ℝ 1 (actualCofactorMatrixFormTwo :
      (E →L[ℝ] E →L[ℝ] ℝ) → Mat) := ContinuousLinearMap.contDiff actualCofactorMatrixFormTwo
  have hM : ContDiffOn ℝ 1 (fun x => actualCofactorMatrixFormTwo (realHessian u x)) U :=
    hF.comp_contDiffOn hH
  intro i j
  apply (contDiffOn_const.mul (contDiffOn_pi.mp (contDiffOn_pi.mp hM i) j)).congr
  intro x hx
  rw [ha x hx,actual_cofactor_matrix_form_eq_two
    ((hu.contDiffAt (hU.mem_nhds hx)).of_le (by norm_num))]
  rfl

theorem actual_C3_scaled_cofactor_entry_derivative_two
    {U : Set E} (hU : IsOpen U) {u : E → ℝ} (hu : ContDiffOn ℝ 3 u U)
    {a : E → Mat} {c : ℝ} (ha : ∀ y ∈ U, a y=c⁻¹ • complexCofactorCoeff u y)
    {x : E} (hx : x ∈ U) (v : E) (i j : Fin (2+2)) :
    fderiv ℝ (fun y => a y i j) x v=
      c⁻¹*actualCofactorMatrixFormTwo (fderiv ℝ (realHessian u) x v) i j := by
  have hu3 := hu.contDiffAt (hU.mem_nhds hx)
  have hH : DifferentiableAt ℝ (realHessian u) x :=
    ((hu3.fderiv_right (m := 2) (by norm_num)).fderiv_right
      (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have he : (fun y => a y i j) =ᶠ[𝓝 x]
      (fun y => c⁻¹*actualCofactorMatrixFormTwo (realHessian u y) i j) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    rw [ha y hy,actual_cofactor_matrix_form_eq_two
      ((hu.contDiffAt (hU.mem_nhds hy)).of_le (by norm_num))]
    rfl
  let ev : Mat →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj j : (Fin (2+2) → ℝ) →L[ℝ] ℝ).comp
      (ContinuousLinearMap.proj i : Mat →L[ℝ] (Fin (2+2) → ℝ))
  have hd := ((ev.comp actualCofactorMatrixFormTwo).hasFDerivAt.comp x hH.hasFDerivAt).const_mul c⁻¹
  have hev (M : Mat) : ev M=M i j := rfl
  rw [he.fderiv_eq]
  have hh := congrArg (fun L : E →L[ℝ] ℝ => L v) hd.fderiv
  simpa only [Function.comp_apply,ContinuousLinearMap.comp_apply,
    hev,_root_.smul_apply,smul_eq_mul] using hh

theorem actual_C3_scaled_cofactor_first_variation_equation_two
    {U : Set E} (hU : IsOpen U) {u rho : E → ℝ}
    (hu : ContDiffOn ℝ 3 u U) (hrho : ContDiffOn ℝ 1 rho U)
    (hpos : ∀ x ∈ U, (complexHessian realDirections imagDirections u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian realDirections imagDirections u x).det=(rho x : ℂ))
    {c : ℝ} {a : E → Mat} (ha : ∀ x ∈ U, a x=c⁻¹ • complexCofactorCoeff u x)
    (v : E) {x : E} (hx : x ∈ U) :
    (∑ i, ∑ j, a x i j*euclideanHessian (fun y => fderiv ℝ u y v) x i j)=
      c⁻¹*fderiv ℝ rho x v := by
  have hne (y : E) (hy : y ∈ U) : rho y ≠ 0 := by
    have hh := (Complex.pos_iff.mp (hpos y hy).det_pos).1
    rw [hdet y hy,Complex.ofReal_re] at hh
    exact hh.ne'
  have hL : linearizedCMAOperatorTwo realDirections imagDirections u
      (fun y => fderiv ℝ u y v) x=fderiv ℝ rho x v/rho x :=
    directionalDerivative_variable_density_two hU hu hrho realDirections imagDirections hdet hne hx v
  have hcontract := complexCofactor_contraction_eq_density_linearized_two (hpos x hx)
    (fun y => fderiv ℝ u y v)
  rw [hdet x hx,Complex.ofReal_re,hL] at hcontract
  have hzero : (∑ i, ∑ j, complexCofactorCoeff u x i j*
      euclideanHessian (fun y => fderiv ℝ u y v) x i j)=fderiv ℝ rho x v :=
    hcontract.trans (by field_simp [hne x hx])
  rw [ha x hx]
  simp only [Matrix.smul_apply,smul_eq_mul,mul_assoc,← Finset.mul_sum,hzero]

theorem actual_C3_scaled_cofactor_second_variation_weak_ball_two
    {U : Set E} (hU : IsOpen U) {u rho : E → ℝ}
    (hu : ContDiffOn ℝ 3 u U) (hrho : ContDiffOn ℝ 2 rho U)
    (hpos : ∀ x ∈ U, (complexHessian realDirections imagDirections u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian realDirections imagDirections u x).det=(rho x : ℂ))
    {c : ℝ} (A : EllipticCoeff (2+2) U)
    (hA : ∀ x ∈ U, A.a x=c⁻¹ • complexCofactorCoeff u x)
    {x₀ : E} {r : ℝ} (hclosed : closedBall x₀ r ⊆ U) (v w : E) :
    ActualScalarWeakEquationTwo (A.restrict (ball_subset_closedBall.trans hclosed))
      (actualCofactorSecondSourceTwo u rho c v w) (fun x => realHessian u x w v) := by
  let p : E → ℝ := fun x => fderiv ℝ u x v
  let f : E → ℝ := fun x => c⁻¹*fderiv ℝ rho x v
  have hp : ContDiffOn ℝ 2 p U :=
    (hu.fderiv_of_isOpen hU (m := 2) (by norm_num)).clm_apply contDiffOn_const
  have hf : ContDiffOn ℝ 1 f U :=
    contDiffOn_const.mul ((hrho.fderiv_of_isOpen hU (m := 1) (by norm_num)).clm_apply contDiffOn_const)
  have hreg := actual_C3_scaled_cofactor_C1_two hU hu hA
  have hsub : ball x₀ r ⊆ U := ball_subset_closedBall.trans hclosed
  have hcol (j : Fin (2+2)) : HasWeakDiv (fun _ => 0)
      (fun x => WithLp.toLp 2 (fun i => A.a x i j)) (ball x₀ r) := by
    have hbase := actual_C2_cofactor_column_hasWeakDiv_zero_two isOpen_ball
      ((hu.of_le (by norm_num)).mono hsub) j
    apply actual_hasWeakDiv_zero_congr_on_two isOpen_ball
      (actual_hasWeakDiv_zero_const_smul_two hbase c⁻¹)
    intro x hx
    ext i
    exact (congrArg (fun M : Mat => M i j) (hA x (hsub hx))).symm
  have hflux : HasWeakDiv f (fun x => matMulE (A.a x) (smoothGradField p x)) (ball x₀ r) := by
    have h := actual_C2_gradient_flux_hasWeakDiv_two hU hclosed
      (fun i j => (hreg i j).continuousOn.mono hclosed) hcol hp
    apply actual_hasWeakDiv_congr_on_two isOpen_ball h (fun _ _ => rfl)
    intro x hx
    exact actual_C3_scaled_cofactor_first_variation_equation_two hU hu
      (hrho.of_le (by norm_num)) hpos hdet hA v (hsub hx)
  have hweak := actual_C1_coefficient_C2_directional_weak_two hU hp hf hclosed
    (A.restrict hsub) hreg hcol hflux w
  have hsource : (fun x => -(fderiv ℝ f x w)+
      ∑ i, ∑ j, fderiv ℝ (fun y => A.a y i j) x w*euclideanHessian p x i j)
      =ᵐ[volume.restrict (ball x₀ r)] actualCofactorSecondSourceTwo u rho c v w := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    have hxU := hsub hx
    have hr2 := hrho.contDiffAt (hU.mem_nhds hxU)
    have hfd : fderiv ℝ f x w=c⁻¹*realHessian rho x w v := by
      rw [show f=(fun y => c⁻¹*fderiv ℝ rho y v) by rfl,
        fderiv_const_mul (((hr2.fderiv_right (m := 1) (by norm_num)).clm_apply
          contDiffAt_const).differentiableAt (by norm_num))]
      simp only [_root_.smul_apply,smul_eq_mul]
      congr 1
      simpa only [ContinuousLinearMap.zero_apply,map_zero,add_zero] using
        fderiv_directional_affine_apply hr2 (0 : E →L[ℝ] E) v w
    have hcorr : (∑ i, ∑ j, fderiv ℝ (fun y => A.a y i j) x w*euclideanHessian p x i j)=
        c⁻¹*actualCofactorThirdCorrectionTwo (fderiv ℝ (realHessian u) x) v w := by
      unfold actualCofactorThirdCorrectionTwo actualCofactorThirdBilinearTwo
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [actual_C3_scaled_cofactor_entry_derivative_two hU hu hA hxU]
      change c⁻¹*actualCofactorMatrixFormTwo (fderiv ℝ (realHessian u) x w) i j*
        realHessian (fun y => fderiv ℝ u y v) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)=_
      rw [actual_third_jet_directional_identity_two (hu.contDiffAt (hU.mem_nhds hxU))]
      ring
    rw [hfd,hcorr]
    rfl
  have hq : (fun x => fderiv ℝ p x w)=ᵐ[volume.restrict (ball x₀ r)]
      (fun x => realHessian u x w v) := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    simpa only [p,ContinuousLinearMap.zero_apply,map_zero,add_zero] using
      fderiv_directional_affine_apply
        ((hu.contDiffAt (hU.mem_nhds (hsub hx))).of_le (by norm_num)) (0 : E →L[ℝ] E) v w
  exact actual_scalar_weak_congr_ae_two hq (actual_scalar_weak_source_congr_ae_two hsource hweak)

end PowerConvexity
