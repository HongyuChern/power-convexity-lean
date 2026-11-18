import PowerConvexity.Analysis.ActualDifferentiatedScalarEquationTwo
import PowerConvexity.Analysis.ActualCofactorThirdCorrectionTwo

/-! # Exact second cofactor variation, with its actual quadratic source -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators ComplexOrder Matrix.Norms.Elementwise
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul
attribute [local instance] ahdTripleNormedGroup ahdTripleNormedSpace ahdTripleModule ahdTripleTopology

def actualCofactorSecondSourceTwo (u rho : E → ℝ) (c : ℝ) (v w x : E) : ℝ :=
  -(c⁻¹*realHessian rho x w v)+
    c⁻¹*actualCofactorThirdCorrectionTwo (fderiv ℝ (realHessian u) x) v w

theorem actual_scaled_cofactor_second_variation_equation_two
    {U : Set E} (hU : IsOpen U) {u rho : E → ℝ}
    (hu : ContDiffOn ℝ 4 u U) (hrho : ContDiffOn ℝ 2 rho U)
    (hpos : ∀ x ∈ U, (complexHessian realDirections imagDirections u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian realDirections imagDirections u x).det = (rho x : ℂ))
    {c : ℝ} (A : EllipticCoeff (2+2) U)
    (hA : ∀ x ∈ U, A.a x = c⁻¹ • complexCofactorCoeff u x)
    (v w : E) {x : E} (hx : x ∈ U) :
    (∑ i, ∑ j, A.a x i j*euclideanHessian (fun y => realHessian u y w v) x i j) =
      -actualCofactorSecondSourceTwo u rho c v w x := by
  have hp : ContDiffOn ℝ 3 (fun y => fderiv ℝ u y v) U :=
    (hu.fderiv_of_isOpen hU (m := 3) (by norm_num)).clm_apply contDiffOn_const
  obtain ⟨hreg,hdiv⟩ := actual_scaled_cofactor_C1_divergence_two hU hu hpos hA
  have hd := actual_differentiate_scalar_equation_two hU hreg hp
    (fun y hy => actual_scaled_cofactor_first_variation_equation_two hU hu
      (hrho.of_le (by norm_num)) hpos hdet A hA v y hy) hx w
  have he : (fun y => fderiv ℝ (fun z => fderiv ℝ u z v) y w) =ᶠ[𝓝 x]
      (fun y => realHessian u y w v) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    simpa only [ContinuousLinearMap.zero_apply,map_zero,add_zero] using
      fderiv_directional_affine_apply
        ((hu.contDiffAt (hU.mem_nhds hy)).of_le (by norm_num)) (0 : E →L[ℝ] E) v w
  have heH (i j : Fin (2+2)) :
      euclideanHessian (fun y => fderiv ℝ (fun z => fderiv ℝ u z v) y w) x i j =
        euclideanHessian (fun y => realHessian u y w v) x i j := by
    unfold euclideanHessian
    rw [realHessian_eq_of_eventuallyEq he]
  simp_rw [heH] at hd
  have hr2 := hrho.contDiffAt (hU.mem_nhds hx)
  have hfd : fderiv ℝ (fun y => c⁻¹*fderiv ℝ rho y v) x w =
      c⁻¹*realHessian rho x w v := by
    rw [fderiv_const_mul (((hr2.fderiv_right (m := 1) (by norm_num)).clm_apply
      contDiffAt_const).differentiableAt (by norm_num))]
    simp only [_root_.smul_apply,smul_eq_mul]
    congr 1
    simpa only [ContinuousLinearMap.zero_apply,map_zero,add_zero] using
      fderiv_directional_affine_apply hr2 (0 : E →L[ℝ] E) v w
  rw [hfd] at hd
  have hcorr : (∑ i, ∑ j, fderiv ℝ (fun y => A.a y i j) x w*
      euclideanHessian (fun y => fderiv ℝ u y v) x i j) =
        c⁻¹*actualCofactorThirdCorrectionTwo (fderiv ℝ (realHessian u) x) v w := by
    unfold actualCofactorThirdCorrectionTwo actualCofactorThirdBilinearTwo
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [actual_scaled_cofactor_entry_derivative_two hU hu hA hx]
    change c⁻¹*actualCofactorMatrixFormTwo (fderiv ℝ (realHessian u) x w) i j*
      realHessian (fun y => fderiv ℝ u y v) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) = _
    rw [actual_third_jet_directional_identity_two
      ((hu.contDiffAt (hU.mem_nhds hx)).of_le (by norm_num))]
    ring
  rw [hcorr] at hd
  exact hd.trans (by unfold actualCofactorSecondSourceTwo; ring)

theorem actual_cofactor_second_source_C1_two
    {U : Set E} (hU : IsOpen U) {u rho : E → ℝ}
    (hu : ContDiffOn ℝ 4 u U) (hrho : ContDiffOn ℝ 3 rho U)
    (c : ℝ) (v w : E) : ContDiffOn ℝ 1 (actualCofactorSecondSourceTwo u rho c v w) U := by
  have hH : ContDiffOn ℝ 2 (realHessian u) U :=
    (hu.fderiv_of_isOpen hU (m := 3) (by norm_num)).fderiv_of_isOpen hU (m := 2) (by norm_num)
  have hT : ContDiffOn ℝ 1 (fderiv ℝ (realHessian u)) U :=
    hH.fderiv_of_isOpen hU (m := 1) (by norm_num)
  have hR : ContDiffOn ℝ 1 (realHessian rho) U :=
    (hrho.fderiv_of_isOpen hU (m := 2) (by norm_num)).fderiv_of_isOpen hU (m := 1) (by norm_num)
  have hmatrix : ContDiffOn ℝ 1
      (fun x => actualCofactorMatrixFormTwo (fderiv ℝ (realHessian u) x w)) U := by
    have hTw : ContDiffOn ℝ 1 (fun x => fderiv ℝ (realHessian u) x w) U :=
      hT.clm_apply contDiffOn_const
    have hF : ContDiff ℝ 1 (actualCofactorMatrixFormTwo :
        (E →L[ℝ] E →L[ℝ] ℝ) → Matrix (Fin (2+2)) (Fin (2+2)) ℝ) := by
      exact ContinuousLinearMap.contDiff actualCofactorMatrixFormTwo
    exact hF.comp_contDiffOn hTw
  have hcorr : ContDiffOn ℝ 1
      (fun x => actualCofactorThirdCorrectionTwo (fderiv ℝ (realHessian u) x) v w) U := by
    unfold actualCofactorThirdCorrectionTwo actualCofactorThirdBilinearTwo
    apply ContDiffOn.sum
    intro i _
    apply ContDiffOn.sum
    intro j _
    exact (contDiffOn_pi.mp (contDiffOn_pi.mp hmatrix i) j).mul
      (((hT.clm_apply contDiffOn_const).clm_apply contDiffOn_const).clm_apply contDiffOn_const)
  exact (contDiffOn_const.mul ((hR.clm_apply contDiffOn_const).clm_apply contDiffOn_const)).neg.add
    (contDiffOn_const.mul hcorr)

theorem actual_scaled_cofactor_second_variation_weak_ball_two
    {U : Set E} (hU : IsOpen U) {u rho : E → ℝ}
    (hu : ContDiffOn ℝ 4 u U) (hrho : ContDiffOn ℝ 3 rho U)
    (hpos : ∀ x ∈ U, (complexHessian realDirections imagDirections u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian realDirections imagDirections u x).det = (rho x : ℂ))
    {c : ℝ} (A : EllipticCoeff (2+2) U)
    (hA : ∀ x ∈ U, A.a x = c⁻¹ • complexCofactorCoeff u x)
    {x₀ : E} {r : ℝ} (hclosed : closedBall x₀ r ⊆ U) (v w : E) :
    ActualScalarWeakEquationTwo (A.restrict (ball_subset_closedBall.trans hclosed))
      (actualCofactorSecondSourceTwo u rho c v w) (fun x => realHessian u x w v) := by
  have hsub : ball x₀ r ⊆ U := ball_subset_closedBall.trans hclosed
  have hp : ContDiffOn ℝ 2 (fun x => realHessian u x w v) U :=
    (((hu.fderiv_of_isOpen hU (m := 3) (by norm_num)).fderiv_of_isOpen hU
      (m := 2) (by norm_num)).clm_apply contDiffOn_const).clm_apply contDiffOn_const
  have hfC := actual_cofactor_second_source_C1_two hU hu hrho c v w
  have hf := continuousOn_memLp_two_of_subset_compact measurableSet_ball
    (isCompact_closedBall x₀ r) ball_subset_closedBall (hfC.continuousOn.mono hclosed)
  obtain ⟨hreg,hdiv⟩ := actual_scaled_cofactor_C1_divergence_two hU hu hpos hA
  apply actual_local_classical_scalar_weak_two hU hp hclosed
    (A.restrict hsub) (fun i j => (hreg i j).mono hsub)
    (fun x hx j => hdiv x (hsub hx) j) hf
  intro x hx
  exact actual_scaled_cofactor_second_variation_equation_two hU hu
    (hrho.of_le (by norm_num)) hpos hdet A hA v w (hsub hx)

end PowerConvexity
