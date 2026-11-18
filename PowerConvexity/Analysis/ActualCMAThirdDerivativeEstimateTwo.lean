import PowerConvexity.Analysis.ActualUniformScalarSchauderTwo
import PowerConvexity.Analysis.ActualDirectionalSourceBoundsTwo
import PowerConvexity.Analysis.ActualScaledCofactorHolderTwo
import PowerConvexity.Calculus.ActualThirdJetNormTwo

/-! # Uniform actual third derivatives from the first CMA variation

Only the original C2 bounds, Hessian Holder modulus, density first and second
derivative bounds, and ellipticity constants determine the estimate.
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

theorem actual_uniform_CMA_third_derivative_holder_two
    {r c lam Lambda K P D₁ D₂ alpha : ℝ}
    (hr : 0 < r) (hc : 0 < c) (hlam : 0 < lam) (hLambda : 0 < Lambda)
    (hK : 0 ≤ K) (hP : 0 ≤ P) (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂)
    (halpha : 0 < alpha) (ha1 : alpha ≤ 1) :
    ∃ delta > 0, delta ≤ r/4 ∧ ∃ beta : ℝ, 0 < beta ∧ beta < 1 ∧ ∃ M ≥ 0,
      ∀ x₀ : E, ∀ U : Set E, IsOpen U → closedBall x₀ (2*r) ⊆ U →
      ∀ u rho : E → ℝ, ContDiffOn ℝ 4 u U → ContDiffOn ℝ 2 rho U →
      (∀ x ∈ U, (complexHessian realDirections imagDirections u x).PosDef) →
      (∀ x ∈ U, (complexHessian realDirections imagDirections u x).det = (rho x : ℂ)) →
      (∀ x ∈ U, ‖fderiv ℝ u x‖ ≤ P) →
      (∀ x ∈ U, ‖fderiv ℝ rho x‖ ≤ D₁) →
      (∀ x ∈ U, ‖realHessian rho x‖ ≤ D₂) →
      (∀ x ∈ closedBall x₀ r, ∀ y ∈ closedBall x₀ r,
        ‖realHessian u x-realHessian u y‖ ≤ K*‖x-y‖^alpha) →
      ∀ A : EllipticCoeff (2+2) U, lam ≤ A.lam → A.Λ ≤ Lambda →
      (∀ x ∈ U, A.a x = c⁻¹ • complexCofactorCoeff u x) →
      (∀ x ∈ ball x₀ delta, ‖fderiv ℝ (realHessian u) x‖ ≤ M) ∧
      ∀ x ∈ ball x₀ delta, ∀ y ∈ ball x₀ delta,
        ‖fderiv ℝ (realHessian u) x-fderiv ℝ (realHessian u) y‖ ≤ M*‖x-y‖^beta := by
  let Ka := c⁻¹*‖actualCofactorOperatorFormTwo‖*K
  let Kf := c⁻¹*D₂*max 1 (4*r)
  let F := c⁻¹*D₁
  let N := Real.sqrt (P^2*(volume (ball (0 : E) (2*r))).toReal)
  have hKa : 0 ≤ Ka := by dsimp [Ka]; positivity
  have hKf : 0 ≤ Kf := by dsimp [Kf]; positivity
  have hF : 0 ≤ F := by dsimp [F]; positivity
  obtain ⟨delta,hd,hdr,beta,hbeta,hbeta1,M,hM,hscalar⟩ :=
    actual_uniform_scalar_C2_holder_interior_two hr hlam hLambda hKa hKf hF
      (Real.sqrt_nonneg _) halpha
  refine ⟨delta,hd,hdr,beta,hbeta,hbeta1,M,hM,?_⟩
  intro x₀ U hU hclosed u rho hu hrho hpos hdet hgrad hD1 hD2 hhold A hlo hhi hA
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
  have hBhold (x : E) (hx : x ∈ closedBall x₀ r) (y : E) (hy : y ∈ closedBall x₀ r) :
      ‖actualMatrixOperatorTwo (B.a x)-actualMatrixOperatorTwo (B.a y)‖ ≤ Ka*‖x-y‖^alpha := by
    exact actual_scaled_cofactor_operator_Holder_bound_two
      ((hu.contDiffAt (hU.mem_nhds (hsub (hsmall hx)))).of_le (by norm_num))
      ((hu.contDiffAt (hU.mem_nhds (hsub (hsmall hy)))).of_le (by norm_num))
      hc (hA x (hsub (hsmall hx))) (hA y (hsub (hsmall hy))) (hhold x hx y hy)
  have hvariation (v : E) (hv : ‖v‖ ≤ 1) :
      (∀ x ∈ ball x₀ delta, ‖realHessian (fun y => fderiv ℝ u y v) x‖ ≤ M) ∧
      ∀ x ∈ ball x₀ delta, ∀ y ∈ ball x₀ delta,
        ‖realHessian (fun z => fderiv ℝ u z v) x-
          realHessian (fun z => fderiv ℝ u z v) y‖ ≤ M*‖x-y‖^beta := by
    let p : E → ℝ := fun x => fderiv ℝ u x v
    let f : E → ℝ := fun x => -(c⁻¹*fderiv ℝ rho x v)
    have hp : ContDiffOn ℝ 1 p U :=
      ((hu.fderiv_of_isOpen hU (m := 3) (by norm_num)).clm_apply contDiffOn_const).of_le (by norm_num)
    obtain ⟨hfC,hfbound,hfhold⟩ := actual_unit_directional_density_source_bounds_two hU hrho
      hr hc hD₁ hD₂ halpha ha1 hsub hD1 hD2 v hv
    have hf := continuousOn_memLp_two_of_subset_compact measurableSet_ball
      (isCompact_closedBall x₀ (2*r)) ball_subset_closedBall (hfC.continuousOn.mono hclosed)
    have hpweak := actual_scaled_cofactor_first_variation_weak_ball_two hU hu hrho hpos hdet A hA hclosed v
    let pw := actualLocalClassicalBallWitnessTwo hU hp hclosed
    have hpbound : ∀ x ∈ ball x₀ (2*r), |p x| ≤ P := by
      intro x hx
      have hh := (fderiv ℝ u x).le_opNorm v
      rw [Real.norm_eq_abs] at hh
      exact hh.trans ((mul_le_mul (hgrad x (hsub hx)) hv (norm_nonneg _) hP).trans_eq (mul_one _))
    have hpn : ‖pw.memLp.toLp p‖ ≤ N := actual_ball_L2_norm_bound_of_pointwise_two pw.memLp hP hpbound
    have hout := hscalar x₀ (ball x₀ (2*r)) isOpen_ball isBounded_ball hsmall B
      hlo hhi hBpos (fun i j => (hreg i j).mono hsub) (fun x hx j => hdiv x (hsub hx) j)
      hBhold f p hf (hfC.mono hsub) hfhold (fun x hx => hfbound x (hsub hx))
      (hp.continuousOn.mono hsub) hpweak pw hpn
    exact ⟨fun x hx => (hout.2.1 x hx).2.2,hout.2.2⟩
  constructor
  · intro x hx
    exact actual_third_jet_norm_from_directional_two
      ((hu.contDiffAt (hU.mem_nhds (hδ hx))).of_le (by norm_num)) hM
      (fun v hv => (hvariation v hv.le).1 x hx)
  · intro x hx y hy
    exact actual_third_jet_difference_from_directional_two
      ((hu.contDiffAt (hU.mem_nhds (hδ hx))).of_le (by norm_num))
      ((hu.contDiffAt (hU.mem_nhds (hδ hy))).of_le (by norm_num))
      (mul_nonneg hM (Real.rpow_nonneg (norm_nonneg _) _))
      (fun v hv => (hvariation v hv.le).2 x hx y hy)

end PowerConvexity
