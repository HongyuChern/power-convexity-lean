import PowerConvexity.Analysis.ActualUniformC3SecondSourceTwo
import PowerConvexity.Analysis.ActualC2CofactorHolderSchauderTwo
import PowerConvexity.Analysis.ActualDirectionalRegularityUpgradeTwo
import PowerConvexity.Calculus.ActualFourthJetNormTwo

/-! # Actual C3 to C4 regularity from the genuine second weak variations

Only C3 regularity and the actual third-jet Holder bound enter the source
and coefficient estimates. The displayed second weak equation is the one
remaining input of this local analytic upgrade; it is not inferred by
classically differentiating a C3 potential twice.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators ComplexOrder Matrix.Norms.Elementwise
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul
attribute [local instance] ahdTripleNormedGroup ahdTripleNormedSpace ahdTripleModule ahdTripleTopology

theorem actual_C4_of_C2_unit_hessian_entries_two
    {U : Set E} (hU : IsOpen U) {u : E → ℝ}
    (hu : ContDiffOn ℝ 2 u U)
    (hunit : ∀ v w : E, ‖v‖=1 → ‖w‖=1 →
      ContDiffOn ℝ 2 (fun x => realHessian u x v w) U) :
    ContDiffOn ℝ 4 u U := by
  have hentry (v w : E) : ContDiffOn ℝ 2 (fun x => realHessian u x v w) U := by
    by_cases hv : v=0
    · subst v
      simpa only [map_zero,ContinuousLinearMap.zero_apply] using
        (contDiffOn_const : ContDiffOn ℝ 2 (fun _ : E => (0 : ℝ)) U)
    by_cases hw : w=0
    · subst w
      simpa only [map_zero] using
        (contDiffOn_const : ContDiffOn ℝ 2 (fun _ : E => (0 : ℝ)) U)
    have hvp : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hwp : 0 < ‖w‖ := norm_pos_iff.mpr hw
    let v' := ‖v‖⁻¹ • v
    let w' := ‖w‖⁻¹ • w
    have hv' : ‖v'‖=1 := by
      dsimp only [v']
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hvp),inv_mul_cancel₀ hvp.ne']
    have hw' : ‖w'‖=1 := by
      dsimp only [w']
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hwp),inv_mul_cancel₀ hwp.ne']
    have hev : ‖v‖ • v'=v := by
      dsimp only [v']
      rw [smul_smul,mul_inv_cancel₀ hvp.ne',one_smul]
    have hew : ‖w‖ • w'=w := by
      dsimp only [w']
      rw [smul_smul,mul_inv_cancel₀ hwp.ne',one_smul]
    apply ((contDiffOn_const : ContDiffOn ℝ 2 (fun _ : E => ‖v‖*‖w‖) U).mul
      (hunit v' w' hv' hw')).congr
    intro x hx
    calc
      realHessian u x v w = realHessian u x (‖v‖ • v') (‖w‖ • w') := by rw [hev,hew]
      _ = (‖v‖*‖w‖)*realHessian u x v' w' := by
        simp only [map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul]
        ring
  apply actual_C4_of_C2_second_directional_C2_two hU hu
  intro v w
  apply (hentry w v).congr
  intro x hx
  simpa only [ContinuousLinearMap.zero_apply,map_zero,add_zero] using
    fderiv_directional_affine_apply (hu.contDiffAt (hU.mem_nhds hx))
      (0 : E →L[ℝ] E) v w

theorem actual_uniform_C3_fourth_upgrade_of_second_weak_two
    {r c lam Lambda H M K D₂ D₃ alpha : ℝ}
    (hr : 0 < r) (hc : 0 < c) (hlam : 0 < lam) (hLambda : 0 < Lambda)
    (hH : 0 ≤ H) (hM : 0 ≤ M) (hK : 0 ≤ K) (hD₂ : 0 ≤ D₂) (hD₃ : 0 ≤ D₃)
    (halpha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ delta > 0, delta ≤ r/4 ∧ ∃ Q ≥ 0,
      ∀ x₀ : E, ∀ U : Set E, IsOpen U → ∀ hclosed : closedBall x₀ (2*r) ⊆ U,
      ∀ u rho : E → ℝ, ContDiffOn ℝ 3 u U → ContDiffOn ℝ 3 rho U →
      (∀ x ∈ U, (complexHessian realDirections imagDirections u x).PosDef) →
      (∀ x ∈ U, ‖realHessian u x‖ ≤ H) →
      (∀ x ∈ U, ‖fderiv ℝ (realHessian u) x‖ ≤ M) →
      (∀ x ∈ ball x₀ (2*r), ∀ y ∈ ball x₀ (2*r),
        ‖fderiv ℝ (realHessian u) x-fderiv ℝ (realHessian u) y‖ ≤ K*‖x-y‖^alpha) →
      (∀ x ∈ U, ‖realHessian rho x‖ ≤ D₂) →
      (∀ x ∈ U, ‖fderiv ℝ (realHessian rho) x‖ ≤ D₃) →
      ∀ A : EllipticCoeff (2+2) U, lam ≤ A.lam → A.Λ ≤ Lambda →
      (∀ x ∈ U, A.a x=c⁻¹ • complexCofactorCoeff u x) →
      (∀ v w : E, ActualScalarWeakEquationTwo
        (A.restrict (ball_subset_closedBall.trans hclosed))
        (actualCofactorSecondSourceTwo u rho c v w) (fun x => realHessian u x w v)) →
      ContDiffOn ℝ 4 u (ball x₀ delta) ∧
      (∀ x ∈ ball x₀ delta, ‖fderiv ℝ (fderiv ℝ (realHessian u)) x‖ ≤ Q) ∧
      ∀ x ∈ ball x₀ delta, ∀ y ∈ ball x₀ delta,
        ‖fderiv ℝ (fderiv ℝ (realHessian u)) x-
          fderiv ℝ (fderiv ℝ (realHessian u)) y‖ ≤ Q*‖x-y‖^alpha := by
  let KH := M*max 1 (4*r)
  let Kf := c⁻¹*D₃*max 1 (4*r)+c⁻¹*(32*‖actualCofactorMatrixFormTwo‖*M*K)
  let F := c⁻¹*D₂+c⁻¹*(16*‖actualCofactorMatrixFormTwo‖*M^2)
  let N := Real.sqrt (H^2*(volume (ball (0 : E) (2*r))).toReal)
  have hKH : 0 ≤ KH := by dsimp only [KH]; positivity
  have hKf : 0 ≤ Kf := by dsimp only [Kf]; positivity
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  obtain ⟨delta,hd,hdr,Q,hQ,hscalar⟩ := actual_uniform_C2_cofactor_weak_holder_interior_two
    hr hc hlam hLambda hKH hKf hF (Real.sqrt_nonneg _) halpha ha1
  refine ⟨delta,hd,hdr,Q,hQ,?_⟩
  intro x₀ U hU hclosed u rho hu hrho hpos hHess hthird hhold hD2 hD3 A hlo hhi hA hweak
  have hsub : ball x₀ (2*r) ⊆ U := ball_subset_closedBall.trans hclosed
  have hsmall : closedBall x₀ r ⊆ ball x₀ (2*r) := closedBall_subset_ball (by linarith)
  have hδ : ball x₀ delta ⊆ U := (ball_subset_ball (by linarith : delta ≤ 2*r)).trans hsub
  have hHhold := actual_Hessian_holder_from_third_bound_two hU hu hM halpha ha1.le hsub hthird
  have hvariation (v w : E) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
      ContDiffOn ℝ 2 (fun x => realHessian u x w v) (ball x₀ delta) ∧
      (∀ x ∈ ball x₀ delta, ‖realHessian (fun y => realHessian u y w v) x‖ ≤ Q) ∧
      ∀ x ∈ ball x₀ delta, ∀ y ∈ ball x₀ delta,
        ‖realHessian (fun z => realHessian u z w v) x-
          realHessian (fun z => realHessian u z w v) y‖ ≤ Q*‖x-y‖^alpha := by
    let p : E → ℝ := fun x => realHessian u x w v
    let f := actualCofactorSecondSourceTwo u rho c v w
    have hp : ContDiffOn ℝ 1 p U :=
      (((hu.fderiv_of_isOpen hU (m := 2) (by norm_num)).fderiv_of_isOpen hU
        (m := 1) (by norm_num)).clm_apply contDiffOn_const).clm_apply contDiffOn_const
    obtain ⟨hfC,hfbound,hfhold⟩ := actual_C3_unit_second_variation_source_bounds_two
      hU hu hrho hc hM hK hD₂ hD₃ halpha ha1.le hsub hthird hhold hD2 hD3 v w hv hw
    have hf := continuousOn_memLp_two_of_subset_compact measurableSet_ball
      (isCompact_closedBall x₀ (2*r)) ball_subset_closedBall (hfC.mono hclosed)
    let pw := actualLocalClassicalBallWitnessTwo hU hp hclosed
    have hpbound : ∀ x ∈ ball x₀ (2*r), |p x| ≤ H := by
      intro x hx
      exact actual_bilinear_unit_value_bound_two _ hH (hHess x (hsub hx)) w v hw hv
    have hpn : ‖pw.memLp.toLp p‖ ≤ N := actual_ball_L2_norm_bound_of_pointwise_two pw.memLp hH hpbound
    have hout := hscalar x₀ U hU hclosed u (hu.of_le (by norm_num)) hpos
      (fun x hx y hy => hHhold x (hsmall hx) y (hsmall hy)) A hlo hhi hA f p hf (hfC.mono hsub)
      hfhold (fun x hx => hfbound x (hsub hx)) (hp.continuousOn.mono hsub) (hweak v w) pw hpn
    exact ⟨hout.1,fun x hx => (hout.2.1 x hx).2.2,hout.2.2⟩
  have hu4 : ContDiffOn ℝ 4 u (ball x₀ delta) :=
    actual_C4_of_C2_unit_hessian_entries_two isOpen_ball ((hu.of_le (by norm_num)).mono hδ)
      (fun v w hv hw => (hvariation w v hw.le hv.le).1)
  refine ⟨hu4,?_,?_⟩
  · intro x hx
    exact actual_fourth_jet_norm_from_scalars_two (hu4.contDiffAt (isOpen_ball.mem_nhds hx)) hQ
      (fun v w hv hw => (hvariation w v hw.le hv.le).2.1 x hx)
  · intro x hx y hy
    exact actual_fourth_jet_difference_from_scalars_two
      (hu4.contDiffAt (isOpen_ball.mem_nhds hx)) (hu4.contDiffAt (isOpen_ball.mem_nhds hy))
      (mul_nonneg hQ (Real.rpow_nonneg (norm_nonneg _) _))
      (fun v w hv hw => (hvariation w v hw.le hv.le).2.2 x hx y hy)

end PowerConvexity
