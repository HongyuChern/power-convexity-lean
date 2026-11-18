import PowerConvexity.Calculus.MinkowskiPositiveParameterSpectrumTwo

/-! # A common actual quadratic ball from values alone

The negative radius is chosen on the entire actual truncated closure graph,
including the ball endpoint. No Hessian bound or power-convexity premise is
used. This does not supply boundary spectral positivity or continuity at zero.
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

theorem minkowski_family_exists_common_negative_quadratic_radius_two
    (mu : Measure E) [IsFiniteMeasureOnCompacts mu] [Measure.IsOpenPosMeasure mu]
    {K : Set E} (hQK : IsCompact K) (hKi : (interior K).Nonempty)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {A B : Set E} (hA : IsOpen A) (hB : IsOpen B)
    (hAc : Convex ℝ A) (hBc : Convex ℝ B)
    {rho L eps : ℝ} (hrho : 0 < rho) (hL : 0 ≤ L)
    (heps : 0 < eps) (hepsrho : eps < rho)
    (hballA : closedBall (0 : E) rho ⊆ A) (hballB : closedBall (0 : E) rho ⊆ B)
    (hAb : ∀ x ∈ A, ‖x‖ ≤ L) (hBb : ∀ x ∈ B, ‖x‖ ≤ L)
    {u : I → E → ℝ} (hu : ClassicalMinkowskiFamilyTwo e (fun j => Complex.I • e j) A B u) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ t : I, ∀ q : E → ℝ,
      IsQuadraticPolynomial q → quadraticL2Energy mu K q ≤ eta →
      ∀ x ∈ closure (distanceInteriorDomain (minkowskiDomain t A B) eps),
        u t x+q x < 0 := by
  let S := {p : I × E | p.2 ∈ closure (distanceInteriorDomain (minkowskiDomain p.1 A B) eps)}
  have hS : IsCompact S := (minkowski_distanceInterior_parameterGraphs
    hA hB hAc hBc hrho hL heps hepsrho hballA hballB hAb hBb).2
  have hV (t : I) : IsOpen (minkowskiDomain t A B) :=
    minkowskiDomain_isOpen hA hB ⟨0,hballA (mem_closedBall_self hrho.le)⟩ t
  have hcl (p : I × E) (hp : p ∈ S) : p.2 ∈ minkowskiDomain p.1 A B :=
    (distanceInteriorDomain_closure_subset (hV p.1) heps hp).1
  have hval : ContinuousOn (fun p : I × E => u p.1 p.2) S := by
    apply (hu.joint_continuous hab hA hB hAc hBc hrho hL
      hballA hballB hAb hBb).continuousOn.congr
    intro p hp
    simp only [Set.indicator_of_mem (hcl p hp)]
  have hneg (p : I × E) (hp : p ∈ S) : u p.1 p.2 < 0 :=
    strictPshDirichlet_negative (hV p.1)
      (minkowskiDomain_isCompact_closure hAb hBb p.1.2.1 p.1.2.2)
      (hu p.1).continuous_closure ((hu p.1).1.of_le (by norm_num))
      (hu p.1).2.2.2.2 e (fun j => Complex.I • e j) (hu p.1).2.2.1 p.2 (hcl p hp)
  obtain ⟨eta,heta,hnegative⟩ := exists_quadratic_L2_radius_negative_family
    mu hQK hKi hS (fun p : I × E => u p.1) Prod.snd continuous_snd.continuousOn hval hneg
  exact ⟨eta,heta,fun t q hq hEq x hx => hnegative q hq hEq (t,x) hx⟩

variable [CompleteSpace E]

theorem minkowski_family_exists_common_negative_radius_continuous_positive_minimum_two
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
      ∀ s : I, 0 < (s : ℝ) →
        ContinuousAt (fun t : I => sInf ((fun x =>
          sInf ((fun q : pluriharmonicQuadraticSubmodule e (fun j => Complex.I • e j) =>
            modifiedSigmaTwo e (fun j => Complex.I • e j) (fun y => u t y+q.val.val y) x) ''
            {q | quadraticL2Energy mu K q.val.val ≤ eta})) ''
          closure (distanceInteriorDomain (minkowskiDomain t A (ball 0 R)) eps))) s := by
  obtain ⟨eta,heta,hnegative⟩ := minkowski_family_exists_common_negative_quadratic_radius_two
    mu hQK hKi e hab hA isOpen_ball hconv (convex_ball 0 R) hrho hL heps hepsrho
    hballA hballB hAb hBb hu
  refine ⟨eta,heta,hnegative,?_⟩
  intro s hs
  exact minkowski_family_quadratic_minimum_continuousAt_of_pos_two mu hQK hKi
    hA hconv hK hboundary e hab hR hrho hL heps hepsrho heta.le
    hballA hballB hAb hBb hu J
    (fun t _ q hq hEq x hx => hnegative t q hq.1 hEq x hx) hs

end PowerConvexity
