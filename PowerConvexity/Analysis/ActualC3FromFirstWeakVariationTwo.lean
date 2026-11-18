import PowerConvexity.Analysis.ActualC2CofactorHolderSchauderTwo
import PowerConvexity.Analysis.ActualDirectionalRegularityUpgradeTwo
import PowerConvexity.Analysis.ActualDirectionalSourceBoundsTwo
import PowerConvexity.Calculus.ActualThirdJetNormTwo

/-! # The actual first weak variation upgrades C2 to C3 with the same exponent

The input identity is the full actual H01 equation for each genuine first
directional derivative.  The cofactor background itself is only C2.  The
scalar regularity theorem constructs C2 regularity of those derivatives,
which identifies the actual third derivative of the original potential.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_uniform_C3_from_first_cofactor_weak_two
    {r c lam Lambda K P D₁ D₂ alpha : ℝ}
    (hr : 0 < r) (hc : 0 < c) (hlam : 0 < lam) (hLambda : 0 < Lambda)
    (hK : 0 ≤ K) (hP : 0 ≤ P) (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂)
    (halpha : 0 < alpha) (halpha1 : alpha < 1) :
    ∃ delta > 0, delta ≤ r/4 ∧ ∃ M ≥ 0,
      ∀ x₀ : E, ∀ U : Set E, IsOpen U → ∀ hclosed : closedBall x₀ (2*r) ⊆ U,
      ∀ u rho : E → ℝ, ContDiffOn ℝ 2 u U → ContDiffOn ℝ 2 rho U →
      (∀ x ∈ U, (complexHessian realDirections imagDirections u x).PosDef) →
      (∀ x ∈ U, ‖fderiv ℝ u x‖ ≤ P) →
      (∀ x ∈ U, ‖fderiv ℝ rho x‖ ≤ D₁) →
      (∀ x ∈ U, ‖realHessian rho x‖ ≤ D₂) →
      (∀ x ∈ closedBall x₀ r, ∀ y ∈ closedBall x₀ r,
        ‖realHessian u x-realHessian u y‖ ≤ K*‖x-y‖^alpha) →
      ∀ A : EllipticCoeff (2+2) U, lam ≤ A.lam → A.Λ ≤ Lambda →
      (∀ x ∈ U, A.a x=c⁻¹ • complexCofactorCoeff u x) →
      (∀ v : E, ‖v‖ ≤ 1 →
        ActualScalarWeakEquationTwo (A.restrict (ball_subset_closedBall.trans hclosed))
          (fun x => -(c⁻¹*fderiv ℝ rho x v)) (fun x => fderiv ℝ u x v)) →
      ContDiffOn ℝ 3 u (ball x₀ delta) ∧
      (∀ x ∈ ball x₀ delta, ‖fderiv ℝ (realHessian u) x‖ ≤ M) ∧
      ∀ x ∈ ball x₀ delta, ∀ y ∈ ball x₀ delta,
        ‖fderiv ℝ (realHessian u) x-fderiv ℝ (realHessian u) y‖ ≤ M*‖x-y‖^alpha := by
  let Kf := c⁻¹*D₂*max 1 (4*r)
  let F := c⁻¹*D₁
  let N := Real.sqrt (P^2*(volume (ball (0 : E) (2*r))).toReal)
  have hKf : 0 ≤ Kf := by dsimp [Kf]; positivity
  have hF : 0 ≤ F := by dsimp [F]; positivity
  obtain ⟨delta,hd,hdr,M,hM,hscalar⟩ :=
    actual_uniform_C2_cofactor_weak_holder_interior_two hr hc hlam hLambda hK hKf hF
      (Real.sqrt_nonneg _) halpha halpha1
  refine ⟨delta,hd,hdr,M,hM,?_⟩
  intro x₀ U hU hclosed u rho hu hrho hpos hgrad hD1 hD2 hhold A hlo hhi hA hweak
  have hsub : ball x₀ (2*r) ⊆ U := ball_subset_closedBall.trans hclosed
  have hδ : ball x₀ delta ⊆ U :=
    (ball_subset_ball (by linarith : delta ≤ 2*r)).trans hsub
  have hvariation (v : E) (hv : ‖v‖ ≤ 1) :
      ContDiffOn ℝ 2 (fun y => fderiv ℝ u y v) (ball x₀ delta) ∧
      (∀ x ∈ ball x₀ delta, ‖realHessian (fun y => fderiv ℝ u y v) x‖ ≤ M) ∧
      ∀ x ∈ ball x₀ delta, ∀ y ∈ ball x₀ delta,
        ‖realHessian (fun z => fderiv ℝ u z v) x-
          realHessian (fun z => fderiv ℝ u z v) y‖ ≤ M*‖x-y‖^alpha := by
    let p : E → ℝ := fun x => fderiv ℝ u x v
    let f : E → ℝ := fun x => -(c⁻¹*fderiv ℝ rho x v)
    have hp : ContDiffOn ℝ 1 p U :=
      (hu.fderiv_of_isOpen hU (m := 1) (by norm_num)).clm_apply contDiffOn_const
    obtain ⟨hfC,hfbound,hfhold⟩ := actual_unit_directional_density_source_bounds_two hU hrho
      hr hc hD₁ hD₂ halpha halpha1.le hsub hD1 hD2 v hv
    have hf := continuousOn_memLp_two_of_subset_compact measurableSet_ball
      (isCompact_closedBall x₀ (2*r)) ball_subset_closedBall (hfC.continuousOn.mono hclosed)
    let pw := actualLocalClassicalBallWitnessTwo hU hp hclosed
    have hpbound : ∀ x ∈ ball x₀ (2*r), |p x| ≤ P := by
      intro x hx
      have hh := (fderiv ℝ u x).le_opNorm v
      rw [Real.norm_eq_abs] at hh
      exact hh.trans ((mul_le_mul (hgrad x (hsub hx)) hv (norm_nonneg _) hP).trans_eq (mul_one _))
    have hpn : ‖pw.memLp.toLp p‖ ≤ N := actual_ball_L2_norm_bound_of_pointwise_two pw.memLp hP hpbound
    have hout := hscalar x₀ U hU hclosed u hu hpos hhold A hlo hhi hA
      f p hf (hfC.continuousOn.mono hsub) hfhold (fun x hx => hfbound x (hsub hx))
      (hp.continuousOn.mono hsub) (hweak v hv) pw hpn
    exact ⟨hout.1,fun x hx => (hout.2.1 x hx).2.2,hout.2.2⟩
  have hu3 : ContDiffOn ℝ 3 u (ball x₀ delta) :=
    actual_C3_of_C1_unit_directional_C2_two isOpen_ball
      ((hu.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).mono hδ)
      (fun v hv => (hvariation v hv).1)
  refine ⟨hu3,?_,?_⟩
  · intro x hx
    exact actual_third_jet_norm_from_directional_two
      (hu3.contDiffAt (isOpen_ball.mem_nhds hx)) hM
      (fun v hv => (hvariation v hv.le).2.1 x hx)
  · intro x hx y hy
    exact actual_third_jet_difference_from_directional_two
      (hu3.contDiffAt (isOpen_ball.mem_nhds hx))
      (hu3.contDiffAt (isOpen_ball.mem_nhds hy))
      (mul_nonneg hM (Real.rpow_nonneg (norm_nonneg _) _))
      (fun v hv => (hvariation v hv.le).2.2 x hx y hy)

end PowerConvexity
