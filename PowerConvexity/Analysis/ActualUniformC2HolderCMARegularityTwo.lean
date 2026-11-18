import PowerConvexity.Analysis.ActualUniformC2CMAFourthRegularityTwo
import CHS.Analysis.LocalEllipticity

/-! # Actual interior C4 regularity from C2 Holder Monge-Ampere data

Compact interior balls supply every derivative bound and the actual
cofactor ellipticity. The first and second true weak variations then
upgrade the same C2 potential. No classical inverse or additional weak
solution is assumed in this regularity statement.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3400000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul
attribute [local instance] ahdTripleNormedGroup ahdTripleNormedSpace ahdTripleModule ahdTripleTopology

theorem actual_C2_holder_CMA_C4_two
    {U : Set E} (hU : IsOpen U) {u rho : E → ℝ}
    (hu : ContDiffOn ℝ 2 u U) (hrho : ContDiffOn ℝ 3 rho U)
    (hpos : ∀ x ∈ U, (complexHessian realDirections imagDirections u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian realDirections imagDirections u x).det=(rho x : ℂ))
    {K alpha : ℝ} (hK : 0 ≤ K) (halpha : 0 < alpha) (halpha1 : alpha < 1)
    (hhold : ∀ x ∈ U, ∀ y ∈ U,
      ‖realHessian u x-realHessian u y‖ ≤ K*‖x-y‖^alpha) :
    ContDiffOn ℝ 4 u U := by
  have hDu : ContDiffOn ℝ 1 (fderiv ℝ u) U := hu.fderiv_of_isOpen hU (m := 1) (by norm_num)
  have hHu : ContDiffOn ℝ 0 (realHessian u) U := hDu.fderiv_of_isOpen hU (m := 0) (by norm_num)
  have hDrho : ContDiffOn ℝ 2 (fderiv ℝ rho) U := hrho.fderiv_of_isOpen hU (m := 2) (by norm_num)
  have hHrho : ContDiffOn ℝ 1 (realHessian rho) U := hDrho.fderiv_of_isOpen hU (m := 1) (by norm_num)
  have hTrho : ContDiffOn ℝ 0 (fderiv ℝ (realHessian rho)) U := hHrho.fderiv_of_isOpen hU (m := 0) (by norm_num)
  have hcof := actual_C2_cofactor_continuousOn_two hU hu
  intro x hx
  obtain ⟨R,hR,hball⟩ := Metric.isOpen_iff.mp hU x hx
  let b := R/2
  have hb : 0 < b := half_pos hR
  have hclosed : closedBall x b ⊆ U := (closedBall_subset_ball (half_lt_self hR)).trans hball
  let V := ball x b
  have hVU : V ⊆ U := ball_subset_closedBall.trans hclosed
  let r := b/8
  have hr : 0 < r := by dsimp only [r]; positivity
  have h4r : closedBall x (4*r) ⊆ V := closedBall_subset_ball (by dsimp only [r]; linarith)
  have hsmall : closedBall x r ⊆ V := closedBall_subset_ball (by dsimp only [r]; linarith)
  obtain ⟨c,hc,A,hA⟩ := exists_normalizedEllipticCoeff_on_ball hb
    (fun i j => (continuousOn_pi.mp (continuousOn_pi.mp hcof i) j).mono hclosed)
    (fun y hy => complexCofactorCoeff_posDef (hpos y (hclosed hy)))
  obtain ⟨P₀,hP₀⟩ := (isCompact_closedBall x b).exists_bound_of_continuousOn
    (f := fderiv ℝ u) (hDu.continuousOn.mono hclosed)
  obtain ⟨H₀,hH₀⟩ := (isCompact_closedBall x b).exists_bound_of_continuousOn
    (f := realHessian u) (hHu.continuousOn.mono hclosed)
  obtain ⟨D₁₀,hD₁₀⟩ := (isCompact_closedBall x b).exists_bound_of_continuousOn
    (f := fderiv ℝ rho) (hDrho.continuousOn.mono hclosed)
  obtain ⟨D₂₀,hD₂₀⟩ := (isCompact_closedBall x b).exists_bound_of_continuousOn
    (f := realHessian rho) (hHrho.continuousOn.mono hclosed)
  obtain ⟨D₃₀,hD₃₀⟩ := (isCompact_closedBall x b).exists_bound_of_continuousOn
    (f := fderiv ℝ (realHessian rho)) (hTrho.continuousOn.mono hclosed)
  obtain ⟨delta,hd,_,M₃,M₄,_,_,hupgrade⟩ := actual_uniform_C2_CMA_fourth_regularity_two
    hr hc A.1.hlam A.1.Λ_pos hK
    (show 0 ≤ max P₀ 0 from le_max_right _ _)
    (show 0 ≤ max H₀ 0 from le_max_right _ _)
    (show 0 ≤ max D₁₀ 0 from le_max_right _ _)
    (show 0 ≤ max D₂₀ 0 from le_max_right _ _)
    (show 0 ≤ max D₃₀ 0 from le_max_right _ _) halpha halpha1
  have hlocal := hupgrade x V isOpen_ball h4r u rho (hu.mono hVU) (hrho.mono hVU)
    (fun z hz => hpos z (hVU hz)) (fun z hz => hdet z (hVU hz))
    (fun z hz => (hP₀ z (ball_subset_closedBall hz)).trans (le_max_left _ _))
    (fun z hz => (hH₀ z (ball_subset_closedBall hz)).trans (le_max_left _ _))
    (fun z hz => (hD₁₀ z (ball_subset_closedBall hz)).trans (le_max_left _ _))
    (fun z hz => (hD₂₀ z (ball_subset_closedBall hz)).trans (le_max_left _ _))
    (fun z hz => (hD₃₀ z (ball_subset_closedBall hz)).trans (le_max_left _ _))
    (fun z hz y hy => hhold z (hVU (hsmall hz)) y (hVU (hsmall hy))) A.1 le_rfl le_rfl hA
  exact (hlocal.1.contDiffAt (ball_mem_nhds x hd)).contDiffWithinAt

end PowerConvexity
