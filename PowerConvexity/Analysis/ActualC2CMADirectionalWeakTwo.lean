import PowerConvexity.Analysis.ActualTranslatedC2SecantFluxTwo
import PowerConvexity.Analysis.ActualWeakDivergenceBoundedLimitTwo

/-! # Actual first weak linearization of a C2 complex Monge-Ampere solution

The proof uses exact determinant secants of the original translated potential,
compact C2 bounds and the actual dominated weak-divergence limit.  It does not
assume a third derivative of the potential or a first derivative of its
cofactor matrix.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators Matrix.Norms.Elementwise
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] atjInstance1 atjInstance2 atjInstance3 atjInstance4 atjInstance5 atjInstance6

theorem actual_C2_CMA_directional_hasWeakDiv_two
    {U : Set E} (hU : IsOpen U) {u rho : E → ℝ}
    (hu : ContDiffOn ℝ 2 u U) (hrho : ContDiffOn ℝ 1 rho U)
    (hdet : ∀ x ∈ U, (complexHessian realDirections imagDirections u x).det.re=rho x)
    {c : E} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hclosed : closedBall c R ⊆ U) (v : E) :
    HasWeakDiv (fun x => fderiv ℝ rho x v)
      (fun x => matMulE (complexCofactorCoeff u x)
        (smoothGradField (fun y => fderiv ℝ u y v) x)) (ball c r) := by
  let m : ℝ := (r+R)/2
  have hrm : r < m := by dsimp only [m]; linarith
  have hmR : m < R := by dsimp only [m]; linarith
  have hsmallsub : closedBall c r ⊆ U :=
    (closedBall_subset_closedBall hrR.le).trans hclosed
  have hmidU : ball c m ⊆ U :=
    (ball_subset_closedBall.trans (closedBall_subset_closedBall hmR.le)).trans hclosed
  have hsmallmid : closedBall c r ⊆ ball c m := closedBall_subset_ball hrm
  have hshift_bound (h : ℝ) (hh : ‖h • v‖ < R-m) (x : E) (hx : x ∈ ball c m) :
      x+h • v ∈ closedBall c R := by
    rw [mem_closedBall,dist_eq_norm]
    have hx' : ‖x-c‖ < m := by simpa only [mem_ball,dist_eq_norm] using hx
    calc
      ‖x+h • v-c‖ = ‖(x-c)+h • v‖ := by congr 1; abel
      _ ≤ ‖x-c‖+‖h • v‖ := norm_add_le _ _
      _ ≤ R := by linarith
  have ht0 : Tendsto (fun h : ℝ => ‖h • v‖) (𝓝[≠] 0) (𝓝 (0 : ℝ)) := by
    have ht : Tendsto (fun h : ℝ => h) (𝓝[≠] 0) (𝓝 (0 : ℝ)) := nhdsWithin_le_nhds
    simpa only [zero_smul,norm_zero] using
      (ht.smul (tendsto_const_nhds : Tendsto (fun _ : ℝ => v) (𝓝[≠] 0) (𝓝 v))).norm
  have hsmall : ∀ᶠ h : ℝ in 𝓝[≠] 0, ‖h • v‖ < R-m :=
    ht0.eventually (gt_mem_nhds (by linarith))
  have hnz : ∀ᶠ h : ℝ in 𝓝[≠] 0, h ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact hh
  have hC : ContinuousOn (complexCofactorCoeff u) U := actual_C2_cofactor_continuousOn_two hU hu
  have hD : ContinuousOn (fderiv ℝ u) U :=
    (hu.fderiv_of_isOpen hU (m := 1) (by norm_num)).continuousOn
  have hH : ContinuousOn (realHessian u) U :=
    ((hu.fderiv_of_isOpen hU (m := 1) (by norm_num)).fderiv_of_isOpen hU
      (m := 0) (by norm_num)).continuousOn
  have hDrho : ContinuousOn (fderiv ℝ rho) U :=
    (hrho.fderiv_of_isOpen hU (m := 0) (by norm_num)).continuousOn
  obtain ⟨B0,hB0⟩ := (isCompact_closedBall c R).exists_bound_of_continuousOn
    ((actualMatrixOperatorTwo.continuous.comp_continuousOn hC).mono hclosed)
  obtain ⟨B1,hB1⟩ := (isCompact_closedBall c R).exists_bound_of_continuousOn
    (f := realHessian u) (hH.mono hclosed)
  obtain ⟨B2,hB2⟩ := (isCompact_closedBall c R).exists_bound_of_continuousOn
    (f := fderiv ℝ rho) (hDrho.mono hclosed)
  let M := max B0 0
  let H := max B1 0
  let D := max B2 0
  have hM : 0 ≤ M := le_max_right _ _
  have hH0 : 0 ≤ H := le_max_right _ _
  have hD0 : 0 ≤ D := le_max_right _ _
  have hA_bound : ∀ x ∈ closedBall c R,
      ‖actualMatrixOperatorTwo (complexCofactorCoeff u x)‖ ≤ M :=
    fun x hx => (hB0 x hx).trans (le_max_left _ _)
  have hH_bound : ∀ x ∈ closedBall c R, ‖realHessian u x‖ ≤ H :=
    fun x hx => (hB1 x hx).trans (le_max_left _ _)
  have hD_bound : ∀ x ∈ closedBall c R, ‖fderiv ℝ rho x‖ ≤ D :=
    fun x hx => (hB2 x hx).trans (le_max_left _ _)
  apply actual_hasWeakDiv_of_common_bounded_limit_two
    (l := 𝓝[≠] (0 : ℝ)) (F := actualTranslatedC2SecantFluxTwo u v)
    (g := actualLineDifferenceQuotientTwo rho v)
  · filter_upwards [hsmall] with h hh
    exact actual_translated_C2_secant_hasWeakDiv_two hU isOpen_ball hmidU hu hdet hsmallmid v h
      (fun x hx => hclosed (hshift_bound h hh x hx))
  · filter_upwards [hsmall] with h hh
    have ht : MapsTo (fun x => x+h • v) (closedBall c r) U :=
      fun x hx => hclosed (hshift_bound h hh x (hsmallmid hx))
    have hmap : ContinuousOn (fun x : E => x+h • v) (closedBall c r) :=
      continuousOn_id.add continuousOn_const
    have hC0 := hC.mono hsmallsub
    have hC1 := hC.comp hmap ht
    have hQ : ContinuousOn
        (actualLineDifferenceQuotientTwo (fderiv ℝ u) v h) (closedBall c r) :=
      ((hD.comp hmap ht).sub (hD.mono hsmallsub)).const_smul h⁻¹
    have hF : ContinuousOn (actualTranslatedC2SecantFluxTwo u v h) (closedBall c r) :=
      (actualMatrixOperatorTwo.continuous.comp_continuousOn
        ((hC0.add hC1).const_smul (1/2 : ℝ))).clm_apply
        (actualCovectorVectorTwo.continuous.comp_continuousOn hQ)
    refine ⟨fun i => (PiLp.continuous_apply 2 (fun _ : Fin (2+2) => ℝ) i).comp_continuousOn hF,?_⟩
    exact ((hrho.continuousOn.comp hmap ht).sub (hrho.continuousOn.mono hsmallsub)).const_smul h⁻¹
  · let C : ℝ := M*(‖actualCovectorVectorTwo‖*(H*‖v‖))+D*‖v‖
    have hCN : 0 ≤ C := by dsimp only [C]; positivity
    refine ⟨C,hCN,?_⟩
    filter_upwards [hsmall,hnz] with h hh hne
    intro x hx
    have hxR := closedBall_subset_closedBall hrR.le hx
    have hxd := hshift_bound h hh x (hsmallmid hx)
    have hF := actual_translated_C2_secant_flux_norm_le_two (convex_closedBall c R)
      (fun y hy => hu.contDiffAt (hU.mem_nhds (hclosed hy))) hM hA_bound hH_bound hne hxR hxd
    have hg := actual_line_difference_quotient_norm_le_two (convex_closedBall c R)
      (fun y hy => (hrho.contDiffAt (hU.mem_nhds (hclosed hy))).differentiableAt (by norm_num))
      hD_bound hne hxR hxd
    rw [Real.norm_eq_abs] at hg
    refine ⟨hF.trans ?_,hg.trans ?_⟩
    · exact le_add_of_nonneg_right (mul_nonneg hD0 (norm_nonneg v))
    · exact le_add_of_nonneg_left (by positivity)
  · intro x hx
    exact actual_translated_C2_secant_flux_tendsto_two hU hu (hsmallsub (ball_subset_closedBall hx)) v
  · intro x hx
    exact actual_line_difference_quotient_tendsto_two
      ((hrho.contDiffAt (hU.mem_nhds (hsmallsub (ball_subset_closedBall hx)))).differentiableAt
        (by norm_num)) v

end PowerConvexity
