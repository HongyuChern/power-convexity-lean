import PowerConvexity.Analysis.ActualUniformPrescribedHolderSchauderTwo
import PowerConvexity.Analysis.ActualUniformClassicalLocalBoundFour

/-! # A fixed-ball classical estimate with continuous Holder source and unchanged exponent -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_uniform_classical_prescribed_holder_four {lam Lambda Ka Kf F B alpha : ℝ}
    (hlam : 0 < lam) (hLambda : 0 < Lambda) (hKa : 0 ≤ Ka) (hKf : 0 ≤ Kf)
    (hF : 0 ≤ F) (hB : 0 ≤ B) (halpha : 0 < alpha) (halpha1 : alpha < 1) :
    ∃ delta > 0, delta ≤ (1/8 : ℝ) ∧ ∃ M ≥ 0,
    ∀ A : EllipticCoeff (2+2) (ball (0 : E) 2), lam ≤ A.lam → A.Λ ≤ Lambda →
    (∀ x ∈ ball (0 : E) 2, (A.a x).PosDef) →
    (∀ i j, ContDiffOn ℝ 1 (fun x => A.a x i j) (ball (0 : E) 2)) →
    (∀ x ∈ ball (0 : E) 2, ∀ j,
      (∑ i, fderiv ℝ (fun y => A.a y i j) x (EuclideanSpace.single i 1))=0) →
    (∀ x ∈ ball (0 : E) 2, ∀ y ∈ ball (0 : E) 2,
      ‖actualMatrixOperatorTwo (A.a x)-actualMatrixOperatorTwo (A.a y)‖ ≤ Ka*‖x-y‖^alpha) →
    ∀ f u : E → ℝ, ContinuousOn f (ball (0 : E) 2) →
    (∀ x ∈ ball (0 : E) 2, ∀ y ∈ ball (0 : E) 2, |f x-f y| ≤ Kf*‖x-y‖^alpha) →
    (∀ x ∈ ball (0 : E) 2, |f x| ≤ F) →
    ContDiffOn ℝ 2 u (ball (0 : E) 2) → (∀ x ∈ ball (0 : E) 2, |u x| ≤ B) →
    (∀ x ∈ ball (0 : E) 2,
      (∑ i, ∑ j, A.a x i j*euclideanHessian u x i j) = -f x) →
    (∀ x ∈ ball (0 : E) delta,
      |u x| ≤ M ∧ ‖fderiv ℝ u x‖ ≤ M ∧ ‖realHessian u x‖ ≤ M) ∧
    ∀ x ∈ ball (0 : E) delta, ∀ y ∈ ball (0 : E) delta,
      ‖realHessian u x-realHessian u y‖ ≤ M*‖x-y‖^alpha := by
  let N₀ := Real.sqrt (B^2*(volume (ball (0 : E) 1)).toReal)
  have hN₀ : 0 ≤ N₀ := Real.sqrt_nonneg _
  obtain ⟨delta,hd,hdr,M,hM,hscalar⟩ :=
    actual_uniform_scalar_C2_prescribed_holder_interior_two (by norm_num : (0 : ℝ) < 1/2)
      hlam hLambda hKa hKf hF hN₀ halpha halpha1
  refine ⟨delta,hd,by norm_num at hdr ⊢; exact hdr,M,hM,?_⟩
  intro A hlo hhi hpos hreg hdiv hhold f u hfC hfhold hfb hu hub hpde
  have hclosed : closedBall (0 : E) 1 ⊆ ball (0 : E) 2 := closedBall_subset_ball (by norm_num)
  have hsub : ball (0 : E) 1 ⊆ ball (0 : E) 2 := ball_subset_ball (by norm_num)
  have hsmall : closedBall (0 : E) (1/2 : ℝ) ⊆ ball (0 : E) 1 :=
    closedBall_subset_ball (by norm_num)
  let A' := A.restrict hsub
  have hf : MemLp f 2 (volume.restrict (ball (0 : E) 1)) :=
    continuousOn_memLp_two_of_subset_compact measurableSet_ball (isCompact_closedBall (0 : E) 1)
      ball_subset_closedBall (hfC.mono hclosed)
  have hw := actual_local_classical_scalar_weak_two isOpen_ball hu hclosed A'
    (fun i j => (hreg i j).mono hsub) (fun z hz j => hdiv z (hsub hz) j) hf
    (fun z hz => hpde z (hsub hz))
  let uw := actualLocalClassicalBallWitnessTwo isOpen_ball (hu.of_le (by norm_num)) hclosed
  have hun : ‖uw.memLp.toLp u‖ ≤ N₀ :=
    actual_ball_L2_norm_bound_of_pointwise_two uw.memLp hB (fun z hz => hub z (hsub hz))
  have hC := hscalar 0 (ball (0 : E) 1) isOpen_ball isBounded_ball hsmall A' hlo hhi
    (fun z hz => hpos z (hsub hz)) (fun i j => (hreg i j).mono hsub)
    (fun z hz j => hdiv z (hsub hz) j)
    (fun z hz w hw => hhold z (hsub (hsmall hz)) w (hsub (hsmall hw)))
    f u hf (hfC.mono hsub) (fun z hz w hw => hfhold z (hsub hz) w (hsub hw))
    (fun z hz => hfb z (hsub hz)) (hu.continuousOn.mono hsub) hw uw hun
  exact hC.2

end PowerConvexity
