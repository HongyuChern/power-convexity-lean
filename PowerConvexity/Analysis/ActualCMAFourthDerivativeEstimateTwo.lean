import PowerConvexity.Analysis.ActualUniformScalarSchauderTwo
import PowerConvexity.Analysis.ActualSecondSourceBoundsTwo
import PowerConvexity.Analysis.ActualScaledCofactorHolderTwo
import PowerConvexity.Calculus.ActualFourthJetNormTwo

/-! # Uniform actual fourth derivatives from the second CMA variation

The quantitative input contains third derivatives, never a fourth derivative bound.
The third derivative estimate is provided independently by the actual first variation.
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
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul
attribute [local instance] ahdTripleNormedGroup ahdTripleNormedSpace ahdTripleModule ahdTripleTopology

theorem actual_uniform_CMA_fourth_derivative_holder_two
    {r c lam Lambda H M K D₂ D₃ alpha : ℝ}
    (hr : 0 < r) (hc : 0 < c) (hlam : 0 < lam) (hLambda : 0 < Lambda)
    (hH : 0 ≤ H) (hM : 0 ≤ M) (hK : 0 ≤ K) (hD₂ : 0 ≤ D₂) (hD₃ : 0 ≤ D₃)
    (halpha : 0 < alpha) (ha1 : alpha ≤ 1) :
    ∃ delta > 0, delta ≤ r/4 ∧ ∃ beta : ℝ, 0 < beta ∧ beta < 1 ∧ ∃ Q ≥ 0,
      ∀ x₀ : E, ∀ U : Set E, IsOpen U → closedBall x₀ (2*r) ⊆ U →
      ∀ u rho : E → ℝ, ContDiffOn ℝ 4 u U → ContDiffOn ℝ 3 rho U →
      (∀ x ∈ U, (complexHessian realDirections imagDirections u x).PosDef) →
      (∀ x ∈ U, (complexHessian realDirections imagDirections u x).det = (rho x : ℂ)) →
      (∀ x ∈ U, ‖realHessian u x‖ ≤ H) →
      (∀ x ∈ U, ‖fderiv ℝ (realHessian u) x‖ ≤ M) →
      (∀ x ∈ ball x₀ (2*r), ∀ y ∈ ball x₀ (2*r),
        ‖fderiv ℝ (realHessian u) x-fderiv ℝ (realHessian u) y‖ ≤ K*‖x-y‖^alpha) →
      (∀ x ∈ U, ‖realHessian rho x‖ ≤ D₂) →
      (∀ x ∈ U, ‖fderiv ℝ (realHessian rho) x‖ ≤ D₃) →
      ∀ A : EllipticCoeff (2+2) U, lam ≤ A.lam → A.Λ ≤ Lambda →
      (∀ x ∈ U, A.a x = c⁻¹ • complexCofactorCoeff u x) →
      (∀ x ∈ ball x₀ delta, ‖fderiv ℝ (fderiv ℝ (realHessian u)) x‖ ≤ Q) ∧
      ∀ x ∈ ball x₀ delta, ∀ y ∈ ball x₀ delta,
        ‖fderiv ℝ (fderiv ℝ (realHessian u)) x-
          fderiv ℝ (fderiv ℝ (realHessian u)) y‖ ≤ Q*‖x-y‖^beta := by
  let Ka := c⁻¹*‖actualCofactorOperatorFormTwo‖*(M*max 1 (4*r))
  let Kf := c⁻¹*D₃*max 1 (4*r)+c⁻¹*(32*‖actualCofactorMatrixFormTwo‖*M*K)
  let F := c⁻¹*D₂+c⁻¹*(16*‖actualCofactorMatrixFormTwo‖*M^2)
  let N := Real.sqrt (H^2*(volume (ball (0 : E) (2*r))).toReal)
  have hKa : 0 ≤ Ka := by dsimp [Ka]; positivity
  have hKf : 0 ≤ Kf := by dsimp [Kf]; positivity
  have hF : 0 ≤ F := by dsimp [F]; positivity
  obtain ⟨delta,hd,hdr,beta,hbeta,hbeta1,Q,hQ,hscalar⟩ :=
    actual_uniform_scalar_C2_holder_interior_two hr hlam hLambda hKa hKf hF
      (Real.sqrt_nonneg _) halpha
  refine ⟨delta,hd,hdr,beta,hbeta,hbeta1,Q,hQ,?_⟩
  intro x₀ U hU hclosed u rho hu hrho hpos hdet hHess hthird hhold hD2 hD3 A hlo hhi hA
  have hsub : ball x₀ (2*r) ⊆ U := ball_subset_closedBall.trans hclosed
  have hsmall : closedBall x₀ r ⊆ ball x₀ (2*r) := closedBall_subset_ball (by linarith)
  have hδ : ball x₀ delta ⊆ U :=
    (ball_subset_ball (by linarith : delta ≤ 2*r)).trans hsub
  let B := A.restrict hsub
  obtain ⟨hreg,hdiv⟩ := actual_scaled_cofactor_C1_divergence_two hU hu hpos hA
  have hBpos (x : E) (hx : x ∈ ball x₀ (2*r)) : (B.a x).PosDef := by
    change (A.a x).PosDef
    rw [hA x (hsub hx)]
    exact (complexCofactorCoeff_posDef (hpos x (hsub hx))).smul (inv_pos.mpr hc)
  have hHhold := actual_Hessian_holder_from_third_bound_two hU
    (hu.of_le (by norm_num)) hM halpha ha1 hsub hthird
  have hBhold (x : E) (hx : x ∈ closedBall x₀ r) (y : E) (hy : y ∈ closedBall x₀ r) :
      ‖actualMatrixOperatorTwo (B.a x)-actualMatrixOperatorTwo (B.a y)‖ ≤ Ka*‖x-y‖^alpha := by
    exact actual_scaled_cofactor_operator_Holder_bound_two
      ((hu.contDiffAt (hU.mem_nhds (hsub (hsmall hx)))).of_le (by norm_num))
      ((hu.contDiffAt (hU.mem_nhds (hsub (hsmall hy)))).of_le (by norm_num))
      hc (hA x (hsub (hsmall hx))) (hA y (hsub (hsmall hy))) (hHhold x (hsmall hx) y (hsmall hy))
  have hvariation (v w : E) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
      (∀ x ∈ ball x₀ delta, ‖realHessian (fun y => realHessian u y w v) x‖ ≤ Q) ∧
      ∀ x ∈ ball x₀ delta, ∀ y ∈ ball x₀ delta,
        ‖realHessian (fun z => realHessian u z w v) x-
          realHessian (fun z => realHessian u z w v) y‖ ≤ Q*‖x-y‖^beta := by
    let p : E → ℝ := fun x => realHessian u x w v
    let f := actualCofactorSecondSourceTwo u rho c v w
    have hp : ContDiffOn ℝ 1 p U :=
      ((((hu.fderiv_of_isOpen hU (m := 3) (by norm_num)).fderiv_of_isOpen hU
        (m := 2) (by norm_num)).clm_apply contDiffOn_const).clm_apply contDiffOn_const).of_le (by norm_num)
    obtain ⟨hfC,hfbound,hfhold⟩ := actual_unit_second_variation_source_bounds_two
      hU hu hrho hc hM hK hD₂ hD₃ halpha ha1 hsub hthird hhold hD2 hD3 v w hv hw
    have hf := continuousOn_memLp_two_of_subset_compact measurableSet_ball
      (isCompact_closedBall x₀ (2*r)) ball_subset_closedBall (hfC.continuousOn.mono hclosed)
    have hpweak := actual_scaled_cofactor_second_variation_weak_ball_two hU hu hrho hpos hdet A hA hclosed v w
    let pw := actualLocalClassicalBallWitnessTwo hU hp hclosed
    have hpbound : ∀ x ∈ ball x₀ (2*r), |p x| ≤ H := by
      intro x hx
      exact actual_bilinear_unit_value_bound_two _ hH (hHess x (hsub hx)) w v hw hv
    have hpn : ‖pw.memLp.toLp p‖ ≤ N := actual_ball_L2_norm_bound_of_pointwise_two pw.memLp hH hpbound
    have hout := hscalar x₀ (ball x₀ (2*r)) isOpen_ball isBounded_ball hsmall B
      hlo hhi hBpos (fun i j => (hreg i j).mono hsub) (fun x hx j => hdiv x (hsub hx) j)
      hBhold f p hf (hfC.mono hsub) hfhold (fun x hx => hfbound x (hsub hx))
      (hp.continuousOn.mono hsub) hpweak pw hpn
    exact ⟨fun x hx => (hout.2.1 x hx).2.2,hout.2.2⟩
  constructor
  · intro x hx
    exact actual_fourth_jet_norm_from_scalars_two
      (hu.contDiffAt (hU.mem_nhds (hδ hx))) hQ
      (fun v w hv hw => (hvariation w v hw.le hv.le).1 x hx)
  · intro x hx y hy
    exact actual_fourth_jet_difference_from_scalars_two
      (hu.contDiffAt (hU.mem_nhds (hδ hx))) (hu.contDiffAt (hU.mem_nhds (hδ hy)))
      (mul_nonneg hQ (Real.rpow_nonneg (norm_nonneg _) _))
      (fun v w hv hw => (hvariation w v hw.le hv.le).2 x hx y hy)

end PowerConvexity
