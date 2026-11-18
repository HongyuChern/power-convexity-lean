import PowerConvexity.Calculus.MinkowskiCommonNegativeRadiusTwo
import PowerConvexity.Calculus.MinkowskiActualDeformationTwo

/-! # Actual ball-start positivity for the same fixed L2 perturbation ball

The ball endpoint is identified by comparison uniqueness. Compactness gives
a positive radius for all its actual truncated-closure points. Intersecting
this radius with the all-parameter negative radius keeps the same ball in
the initial positivity and every positive-parameter minimum. Continuity at
zero and the common boundary spectral collar are not asserted here.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
attribute [local irreducible] modifiedSigmaTwo modifiedK modifiedA modifiedB complexHessian pureHessian complexGradient
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]
local notation "I" => Icc (0 : ℝ) 1

theorem minkowski_family_exists_ball_endpoint_positive_quadratic_radius_two
    (mu : Measure E) [IsFiniteMeasureOnCompacts mu] [Measure.IsOpenPosMeasure mu]
    {K : Set E} (hQK : IsCompact K) (hKi : (interior K).Nonempty)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {A : Set E} (hAn : A.Nonempty) {R eps : ℝ} (hR : 0 < R) (heps : 0 < eps)
    {u : I → E → ℝ} (hu : ClassicalMinkowskiFamilyTwo e (fun j => Complex.I • e j) A (ball 0 R) u) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ q : E → ℝ,
      IsPluriharmonicQuadratic e (fun j => Complex.I • e j) q → quadraticL2Energy mu K q ≤ eta →
      ∀ x ∈ closure (distanceInteriorDomain
          (minkowskiDomain (0 : ℝ) A (ball 0 R)) eps),
        u ⟨0,by norm_num⟩ x+q x < 0 ∧
        0 < modifiedSigmaTwo e (fun j => Complex.I • e j)
          (fun y => u ⟨0,by norm_num⟩ y+q y) x := by
  let t0 : I := ⟨0,by norm_num⟩
  let S := closure (distanceInteriorDomain (minkowskiDomain (0 : ℝ) A (ball (0 : E) R)) eps)
  have he : minkowskiDomain (0 : ℝ) A (ball (0 : E) R) = ball 0 R := minkowskiDomain_zero hAn
  have hcl (x : E) (hx : x ∈ S) : x ∈ ball (0 : E) R := by
    apply (distanceInteriorDomain_closure_subset isOpen_ball heps ?_).1
    simpa only [S,he] using hx
  have hS : IsCompact S := (isCompact_closedBall (0 : E) R).of_isClosed_subset
    isClosed_closure (fun x hx => ball_subset_closedBall (hcl x hx))
  have hdata : ClassicalDirichletDataTwo e (fun j => Complex.I • e j) (ball (0 : E) R) (u t0) := by
    simpa only [t0,he] using hu t0
  have hreg (x : E) (hx : x ∈ S) : ContDiffAt ℝ 2 (u t0) x :=
    (hdata.1.contDiffAt (isOpen_ball.mem_nhds (hcl x hx))).of_le (by norm_num)
  have hval : ContinuousOn (u t0) S := fun x hx => (hreg x hx).continuousAt.continuousWithinAt
  have hD : ContinuousOn (fderiv ℝ (u t0)) S := fun x hx =>
    ((hreg x hx).fderiv_right (m := 1) (by norm_num)).continuousAt.continuousWithinAt
  have hH : ContinuousOn (realHessian (u t0)) S := fun x hx =>
    (((hreg x hx).fderiv_right (m := 1) (by norm_num)).fderiv_right
      (m := 0) (by norm_num)).continuousAt.continuousWithinAt
  have hneg (x : E) (hx : x ∈ S) : u t0 x < 0 := by
    rw [hu.endpoint_zero hab hAn hR (subset_closure (hcl x hx))]
    exact quadraticBallPotential_negative (by norm_num) hR (hcl x hx)
  exact exists_quadratic_L2_radius_negative_and_positive_sigma_family_two mu hQK hKi e hS
    (fun _ : E => u t0) id hreg continuous_id.continuousOn hval hD hH hneg
    (fun x hx => hdata.2.2.1 x (hcl x hx))
    (fun x hx => hu.ball_endpoint_sigma_positive e hab hAn hR (hcl x hx))

variable [CompleteSpace E]

theorem minkowski_family_exists_common_ball_start_radius_two
    (mu : Measure E) [IsFiniteMeasureOnCompacts mu] [Measure.IsOpenPosMeasure mu]
    {K : Set E} (hQK : IsCompact K) (hKi : (interior K).Nonempty)
    {A : Set E} (hA : IsOpen A) (hconv : Convex ℝ A) (hK : IsCompact (closure A))
    (hboundary : HasSmoothLocalDefiningFunction A)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {R rho L eps : ℝ} (hR : 0 < R) (hrho : 0 < rho) (hL : 0 ≤ L)
    (heps : 0 < eps) (hepsrho : eps < rho)
    (hballA : closedBall (0 : E) rho ⊆ A) (hballB : closedBall (0 : E) rho ⊆ ball 0 R)
    (hAb : ∀ x ∈ A, ‖x‖ ≤ L) (hBb : ∀ x ∈ ball (0 : E) R, ‖x‖ ≤ L)
    {u : I → E → ℝ} (hu : ClassicalMinkowskiFamilyTwo e (fun j => Complex.I • e j) A (ball 0 R) u)
    (J : ∀ t, ClosureC2Jet (u t) (minkowskiDomain t A (ball 0 R))) :
    ∃ eta : ℝ, 0 < eta ∧
      (∀ t : I, ∀ q : E → ℝ, IsQuadraticPolynomial q → quadraticL2Energy mu K q ≤ eta →
        ∀ x ∈ closure (distanceInteriorDomain (minkowskiDomain t A (ball 0 R)) eps),
          u t x+q x < 0) ∧
      (∀ q : E → ℝ, IsPluriharmonicQuadratic e (fun j => Complex.I • e j) q →
        quadraticL2Energy mu K q ≤ eta →
        ∀ x ∈ closure (distanceInteriorDomain (minkowskiDomain (0 : ℝ) A (ball 0 R)) eps),
          0 < modifiedSigmaTwo e (fun j => Complex.I • e j)
            (fun y => u ⟨0,by norm_num⟩ y+q y) x) ∧
      ∀ s : I, 0 < (s : ℝ) →
        ContinuousAt (fun t : I => sInf ((fun x =>
          sInf ((fun q : pluriharmonicQuadraticSubmodule e (fun j => Complex.I • e j) =>
            modifiedSigmaTwo e (fun j => Complex.I • e j) (fun y => u t y+q.val.val y) x) ''
            {q | quadraticL2Energy mu K q.val.val ≤ eta})) ''
          closure (distanceInteriorDomain (minkowskiDomain t A (ball 0 R)) eps))) s := by
  obtain ⟨etaN,hetaN,hnegative⟩ := minkowski_family_exists_common_negative_quadratic_radius_two
    mu hQK hKi e hab hA isOpen_ball hconv (convex_ball 0 R) hrho hL heps hepsrho
    hballA hballB hAb hBb hu
  obtain ⟨etaB,hetaB,hball⟩ := minkowski_family_exists_ball_endpoint_positive_quadratic_radius_two
    mu hQK hKi e hab ⟨0,hballA (mem_closedBall_self hrho.le)⟩ hR heps hu
  let eta := min etaN etaB
  have heta : 0 < eta := lt_min hetaN hetaB
  have hN (t : I) (q : E → ℝ) (hq : IsQuadraticPolynomial q)
      (hEq : quadraticL2Energy mu K q ≤ eta) (x : E)
      (hx : x ∈ closure (distanceInteriorDomain (minkowskiDomain t A (ball 0 R)) eps)) :
      u t x+q x < 0 := hnegative t q hq (hEq.trans (min_le_left _ _)) x hx
  refine ⟨eta,heta,hN,?_,?_⟩
  · intro q hq hEq x hx
    exact (hball q hq (hEq.trans (min_le_right _ _)) x hx).2
  · intro s hs
    exact minkowski_family_quadratic_minimum_continuousAt_of_pos_two mu hQK hKi
      hA hconv hK hboundary e hab hR hrho hL heps hepsrho heta.le
      hballA hballB hAb hBb hu J
      (fun t _ q hq hEq x hx => hN t q hq.1 hEq x hx) hs

end PowerConvexity
