import PowerConvexity.Calculus.MinkowskiAllParameterActualMinimumTwo

/-! # One actual boundary perturbation radius after the zero endpoint is solved.
The full actual jet graph supplies one common radius and the same-radius
minimum. The unperturbed actual boundary spectral positivity remains explicit;
no boundary curvature or zero-parameter estimate is added as an assumption.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
attribute [local irreducible] modifiedSigmaTwo modifiedK modifiedA modifiedB complexHessian pureHessian complexGradient
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E] [Nontrivial E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
local notation "I" => Icc (0 : ℝ) 1

theorem minkowski_actual_exists_common_boundary_radius_two
    (μ : Measure E) [IsFiniteMeasureOnCompacts μ] [Measure.IsOpenPosMeasure μ]
    {K : Set E} (hK : IsCompact K) (hKi : (interior K).Nonempty)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {A : Set E} (hAo : IsOpen A) (hA : Convex ℝ A)
    (hAK : IsCompact (closure A)) (hSmooth : HasSmoothLocalDefiningFunction A)
    {R ρ L ε : ℝ} (hR : 0 < R) (hρ : 0 < ρ) (hL : 0 ≤ L) (hε : 0 < ε) (hερ : ε < ρ)
    (hballA : closedBall (0 : E) ρ ⊆ A) (hballB : closedBall (0 : E) ρ ⊆ (ball (0 : E) R))
    (hAb : ∀ x ∈ A, ‖x‖ ≤ L) (hBb : ∀ x ∈ (ball (0 : E) R), ‖x‖ ≤ L)
    {u : I → E → ℝ}
    (hu : ClassicalMinkowskiFamilyTwo e (fun j => Complex.I • e j) A (ball (0 : E) R) u)
    (J : ∀ t, ClosureC2Jet (u t) (minkowskiDomain t A (ball (0 : E) R)))
    (hboundary : ∀ t : I, ∀ x ∈ frontier (distanceInteriorDomain (minkowskiDomain t A (ball (0 : E) R)) ε),
      0 < modifiedSigmaTwo e (fun j => Complex.I • e j) (u t) x) :
    ∃ η > 0,
      (∀ t : I, ∀ q : E → ℝ, IsPluriharmonicQuadratic e (fun j => Complex.I • e j) q →
        quadraticL2Energy μ K q ≤ η →
        ∀ x ∈ closure (distanceInteriorDomain (minkowskiDomain t A (ball (0 : E) R)) ε), u t x+q x < 0) ∧
      (∀ t : I, ∀ q : E → ℝ, IsPluriharmonicQuadratic e (fun j => Complex.I • e j) q →
        quadraticL2Energy μ K q ≤ η →
        ∀ x ∈ frontier (distanceInteriorDomain (minkowskiDomain t A (ball (0 : E) R)) ε),
          0 < modifiedSigmaTwo e (fun j => Complex.I • e j) (fun y => u t y+q y) x) ∧
      Continuous (fun t : I => sInf ((fun x =>
        sInf ((fun q : pluriharmonicQuadraticSubmodule e (fun j => Complex.I • e j) =>
          modifiedSigmaTwo e (fun j => Complex.I • e j) (fun y => u t y+q.val.val y) x) ''
          {q | quadraticL2Energy μ K q.val.val ≤ η})) ''
        closure (distanceInteriorDomain (minkowskiDomain t A (ball (0 : E) R)) ε))) := by
  let S := {p : I × E | p.2 ∈ closure (distanceInteriorDomain (minkowskiDomain p.1 A (ball (0 : E) R)) ε)}
  let F := {p : I × E | p.2 ∈ frontier (distanceInteriorDomain (minkowskiDomain p.1 A (ball (0 : E) R)) ε)}
  have hFS : F ⊆ S := fun p hp => frontier_subset_closure hp
  have hS : IsCompact S := (minkowski_distanceInterior_parameterGraphs
    hAo isOpen_ball hA (convex_ball (0 : E) R) hρ hL hε hερ hballA hballB hAb hBb).2
  have hF : IsCompact F := minkowski_distanceInterior_frontier_parameterGraph_isCompact
    hAo isOpen_ball hA (convex_ball (0 : E) R) hρ hL hε hερ hballA hballB hAb hBb
  have hV (t : I) : IsOpen (minkowskiDomain t A (ball (0 : E) R)) :=
    minkowskiDomain_isOpen hAo isOpen_ball ⟨0,hballA (mem_closedBall_self hρ.le)⟩ t
  have hcl (p : I × E) (hp : p ∈ S) : p.2 ∈ minkowskiDomain p.1 A (ball (0 : E) R) :=
    (distanceInteriorDomain_closure_subset (hV p.1) hε hp).1
  have hreg (p : I × E) (hp : p ∈ S) : ContDiffAt ℝ 2 (u p.1) p.2 :=
    ((hu p.1).1.contDiffAt ((hV p.1).mem_nhds (hcl p hp))).of_le (by norm_num)
  have hpos (p : I × E) (hp : p ∈ S) :
      (complexHessian e (fun j => Complex.I • e j) (u p.1) p.2).PosDef :=
    (hu p.1).2.2.1 p.2 (hcl p hp)
  have hneg (p : I × E) (hp : p ∈ S) : u p.1 p.2 < 0 :=
    strictPshDirichlet_negative (hV p.1)
      (minkowskiDomain_isCompact_closure hAb hBb p.1.2.1 p.1.2.2)
      (hu p.1).continuous_closure ((hu p.1).1.of_le (by norm_num))
      (hu p.1).2.2.2.2 e (fun j => Complex.I • e j) (hu p.1).2.2.1 p.2 (hcl p hp)
  have hj := minkowski_family_actual_jets_continuousOn_distanceClosure_two
    hAo hA hAK hSmooth e hab hR hρ hL hε hballA hballB hAb hBb hu J
  obtain ⟨ηN,hηN,hN⟩ := exists_quadratic_L2_radius_negative_family μ hK hKi hS
    (fun p : I × E => u p.1) Prod.snd continuous_snd.continuousOn hj.1 hneg
  obtain ⟨ηB,hηB,hBd⟩ := exists_quadratic_L2_radius_negative_and_positive_sigma_family_two
    μ hK hKi e hF (fun p : I × E => u p.1) Prod.snd
    (fun p hp => hreg p (hFS hp)) continuous_snd.continuousOn
    (hj.1.mono hFS) (hj.2.1.mono hFS) (hj.2.2.mono hFS)
    (fun p hp => hneg p (hFS hp)) (fun p hp => hpos p (hFS hp))
    (fun p hp => hboundary p.1 p.2 hp)
  let η := min ηN ηB
  have hη : 0 < η := lt_min hηN hηB
  have hnegative (t : I) (q : E → ℝ)
      (hq : IsPluriharmonicQuadratic e (fun j => Complex.I • e j) q)
      (hEq : quadraticL2Energy μ K q ≤ η)
      (x : E) (hx : x ∈ closure (distanceInteriorDomain (minkowskiDomain t A (ball (0 : E) R)) ε)) :
      u t x+q x < 0 := hN q hq.1 (hEq.trans (min_le_left _ _)) (t,x) hx
  refine ⟨η,hη,hnegative,?_,?_⟩
  · intro t q hq hEq x hx
    exact (hBd q hq (hEq.trans (min_le_right _ _)) (t,x) hx).2
  · exact minkowski_family_quadratic_minimum_continuous_two μ hK hKi
      hAo hA hAK hSmooth e hab hR hρ hL hε hερ hη.le hballA hballB hAb hBb hu J hnegative

end PowerConvexity
