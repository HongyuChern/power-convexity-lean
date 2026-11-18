import PowerConvexity.Analysis.ActualC2CofactorQuadraticSourcesTwo
import PowerConvexity.Analysis.ActualContinuousWeakQuadraticClassicalTwo
import PowerConvexity.Analysis.ActualScaledCofactorHolderTwo

/-! # Actual C2 cofactor backgrounds satisfy the continuous-coefficient Schauder hypotheses

The real cofactor of the same C2 potential supplies continuity and the full
weak polynomial identities.  Its Holder constant comes from the actual
Hessian modulus.  No first derivative of the coefficient is assumed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators ComplexOrder Matrix.Norms.Elementwise
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_C2_scaled_cofactor_continuous_closedBall_two
    {V : Set E} (hV : IsOpen V) {u : E → ℝ} (hu : ContDiffOn ℝ 2 u V)
    {x₀ : E} {r k : ℝ} (hclosed : closedBall x₀ r ⊆ V)
    {a : E → Matrix (Fin (2+2)) (Fin (2+2)) ℝ}
    (ha : ∀ x ∈ V, a x=k • complexCofactorCoeff u x) :
    ∀ i j, ContinuousOn (fun x => a x i j) (closedBall x₀ r) := by
  have hc := actual_C2_cofactor_continuousOn_two hV hu
  intro i j
  apply (((continuousOn_pi.mp (continuousOn_pi.mp hc i) j).const_mul k).mono hclosed).congr
  intro x hx
  exact congrArg (fun M : Matrix (Fin (2+2)) (Fin (2+2)) ℝ => M i j)
    (ha x (hclosed hx))

theorem actual_uniform_C2_cofactor_weak_holder_interior_two
    {r c lam Lambda K Kf F N alpha : ℝ}
    (hr : 0 < r) (hc : 0 < c) (hlam : 0 < lam) (hLambda : 0 < Lambda)
    (hK : 0 ≤ K) (hKf : 0 ≤ Kf) (hF : 0 ≤ F) (hN : 0 ≤ N)
    (halpha : 0 < alpha) (halpha1 : alpha < 1) :
    ∃ delta > 0, delta ≤ r/4 ∧ ∃ M ≥ 0,
      ∀ x₀ : E, ∀ V : Set E, IsOpen V → ∀ hclosed : closedBall x₀ (2*r) ⊆ V,
      ∀ u : E → ℝ, ContDiffOn ℝ 2 u V →
      (∀ x ∈ V, (complexHessian realDirections imagDirections u x).PosDef) →
      (∀ x ∈ closedBall x₀ r, ∀ y ∈ closedBall x₀ r,
        ‖realHessian u x-realHessian u y‖ ≤ K*‖x-y‖^alpha) →
      ∀ A : EllipticCoeff (2+2) V, lam ≤ A.lam → A.Λ ≤ Lambda →
      (∀ x ∈ V, A.a x=c⁻¹ • complexCofactorCoeff u x) →
      ∀ f p : E → ℝ,
      MemLp f 2 (volume.restrict (ball x₀ (2*r))) →
      ContinuousOn f (ball x₀ (2*r)) →
      (∀ x ∈ ball x₀ (2*r), ∀ y ∈ ball x₀ (2*r),
        |f x-f y| ≤ Kf*‖x-y‖^alpha) →
      (∀ x ∈ ball x₀ (2*r), |f x| ≤ F) →
      ContinuousOn p (ball x₀ (2*r)) →
      ActualScalarWeakEquationTwo (A.restrict (ball_subset_closedBall.trans hclosed)) f p →
      ∀ pw : MemW1pWitness 2 p (ball x₀ (2*r)), ‖pw.memLp.toLp p‖ ≤ N →
      ContDiffOn ℝ 2 p (ball x₀ delta) ∧
      (∀ x ∈ ball x₀ delta,
        |p x| ≤ M ∧ ‖fderiv ℝ p x‖ ≤ M ∧ ‖realHessian p x‖ ≤ M) ∧
      ∀ x ∈ ball x₀ delta, ∀ y ∈ ball x₀ delta,
        ‖realHessian p x-realHessian p y‖ ≤ M*‖x-y‖^alpha := by
  let Ka := c⁻¹*‖actualCofactorOperatorFormTwo‖*K
  have hKa : 0 ≤ Ka := by dsimp [Ka]; positivity
  obtain ⟨delta,hd,hdr,M,hM,hscalar⟩ :=
    actual_uniform_weak_quadratic_C2_holder_interior_two hr hlam hLambda
      hKa hKf hF hN halpha halpha1
  refine ⟨delta,hd,hdr,M,hM,?_⟩
  intro x₀ V hV hclosed u hu hpos hhold A hlo hhi hA f p hf hfC hfhold hfbound hpC hp pw hpn
  have hsub : ball x₀ (2*r) ⊆ V := ball_subset_closedBall.trans hclosed
  have hsmall : closedBall x₀ r ⊆ ball x₀ (2*r) := closedBall_subset_ball (by linarith)
  let B := A.restrict hsub
  have hBpos (x : E) (hx : x ∈ ball x₀ (2*r)) : (B.a x).PosDef := by
    change (A.a x).PosDef
    rw [hA x (hsub hx)]
    exact (complexCofactorCoeff_posDef (hpos x (hsub hx))).smul (inv_pos.mpr hc)
  have hBc := actual_C2_scaled_cofactor_continuous_closedBall_two hV hu hclosed hA
  have hBreg (i j : Fin (2+2)) :
      ContinuousOn (fun x => B.a x i j) (closure (ball x₀ (2*r))) := by
    exact (hBc i j).mono closure_ball_subset_closedBall
  have hBquad : ActualWeakQuadraticSourcesTwo B :=
    actual_C2_scaled_cofactor_weak_quadratic_sources_two hV hu hclosed B hA
  have hBhold (x : E) (hx : x ∈ closedBall x₀ r) (y : E) (hy : y ∈ closedBall x₀ r) :
      ‖actualMatrixOperatorTwo (B.a x)-actualMatrixOperatorTwo (B.a y)‖ ≤ Ka*‖x-y‖^alpha := by
    exact actual_scaled_cofactor_operator_Holder_bound_two
      (hu.contDiffAt (hV.mem_nhds (hsub (hsmall hx))))
      (hu.contDiffAt (hV.mem_nhds (hsub (hsmall hy))))
      hc (hA x (hsub (hsmall hx))) (hA y (hsub (hsmall hy))) (hhold x hx y hy)
  exact hscalar x₀ (ball x₀ (2*r)) isOpen_ball isBounded_ball hsmall B
    hlo hhi hBpos hBreg hBquad hBhold f p hf hfC hfhold hfbound hpC hp pw hpn

end PowerConvexity
