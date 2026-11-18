import PowerConvexity.Calculus.MinkowskiBallMinimumTwo
import PowerConvexity.Calculus.ActualQuadraticMinimumNoZeroTwo
import PowerConvexity.Analysis.PositiveParameterFirstContact

/-! # Actual deformation with a positive-parameter spectral initialization

Only positive-parameter continuity is used. The same truncation eps and the
same L2 radius eta occur in the minimum, boundary positivity, contact argument
and conclusion. The positive initialization and boundary positivity remain
explicit analytic obligations; this module does not claim to prove them.
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
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
local notation "I" => Icc (0 : ℝ) 1

theorem minkowski_actual_deformation_from_positive_parameter_minimum_two
    (μ : Measure E) [IsFiniteMeasureOnCompacts μ] [Measure.IsOpenPosMeasure μ]
    {K : Set E} (hQK : IsCompact K) (hKi : (interior K).Nonempty)
    {A : Set E} (hA : IsOpen A) (hconv : Convex ℝ A) (hK : IsCompact (closure A))
    (hboundary : HasSmoothLocalDefiningFunction A)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {R rho L eps eta : ℝ} (hR : 0 < R) (hrho : 0 < rho) (hL : 0 ≤ L)
    (heps : 0 < eps) (hepsrho : eps < rho) (heta : 0 < eta)
    (hballA : closedBall (0 : E) rho ⊆ A) (hballB : closedBall (0 : E) rho ⊆ ball 0 R)
    (hAb : ∀ x ∈ A, ‖x‖ ≤ L) (hBb : ∀ x ∈ ball (0 : E) R, ‖x‖ ≤ L)
    {u : I → E → ℝ} (hu : ClassicalMinkowskiFamilyTwo e (fun j => Complex.I • e j) A (ball 0 R) u)
    (J : ∀ t, ClosureC2Jet (u t) (minkowskiDomain t A (ball 0 R)))
    (hnegative : ∀ t : I, 0 < (t : ℝ) → ∀ q : E → ℝ,
      IsPluriharmonicQuadratic e (fun j => Complex.I • e j) q → quadraticL2Energy μ K q ≤ eta →
      ∀ x ∈ closure (distanceInteriorDomain (minkowskiDomain t A (ball 0 R)) eps), u t x+q x < 0)
    (hbd : ∀ t : I, 0 < (t : ℝ) → ∀ q : E → ℝ,
      IsPluriharmonicQuadratic e (fun j => Complex.I • e j) q → quadraticL2Energy μ K q ≤ eta →
      ∀ x ∈ frontier (distanceInteriorDomain (minkowskiDomain t A (ball 0 R)) eps),
        0 < modifiedSigmaTwo e (fun j => Complex.I • e j) (fun y => u t y+q y) x)
    (hanchor : ∃ s : I, 0 < (s : ℝ) ∧
      0 < actualQuadraticSpectralMinimumTwo μ K e eta
        (distanceInteriorDomain (minkowskiDomain s A (ball 0 R)) eps) (u s)) :
    ∀ t : I, 0 < (t : ℝ) → ∀ q : E → ℝ,
      IsPluriharmonicQuadratic e (fun j => Complex.I • e j) q → quadraticL2Energy μ K q ≤ eta →
      (∀ x ∈ closure (distanceInteriorDomain (minkowskiDomain t A (ball 0 R)) eps),
        0 < modifiedSigmaTwo e (fun j => Complex.I • e j) (fun y => u t y+q y) x) ∧
      StrictConvexOn ℝ (distanceInteriorDomain (minkowskiDomain t A (ball 0 R)) eps)
        (powerTransform (fun y => u t y+q y)) := by
  let V : I → Set E := fun t => distanceInteriorDomain (minkowskiDomain t A (ball 0 R)) eps
  let m : I → ℝ := fun t => actualQuadraticSpectralMinimumTwo μ K e eta (V t) (u t)
  have hgeo (t : I) := minkowski_distanceInterior_uniform_geometry hA isOpen_ball
    hconv (convex_ball 0 R) hrho heps hepsrho hballA hballB hAb hBb t
  have hU (t : I) : IsOpen (minkowskiDomain t A (ball 0 R)) :=
    minkowskiDomain_isOpen hA isOpen_ball ⟨0,hballA (mem_closedBall_self hrho.le)⟩ t
  have hcl (t : I) : closure (V t) ⊆ minkowskiDomain t A (ball 0 R) := (hgeo t).2.2.2.2
  have hreg (t : I) (x : E) (hx : x ∈ closure (V t)) : ContDiffAt ℝ 4 (u t) x :=
    (hu t).1.contDiffAt ((hU t).mem_nhds (hcl t hx))
  have hpos (t : I) (x : E) (hx : x ∈ closure (V t)) :
      (complexHessian e (fun j => Complex.I • e j) (u t) x).PosDef :=
    (hu t).2.2.1 x (hcl t hx)
  have hm : ∀ s : I, 0 < (s : ℝ) → ContinuousAt m s := by
    intro s hs
    exact minkowski_family_quadratic_minimum_continuousAt_of_pos_two μ hQK hKi
      hA hconv hK hboundary e hab hR hrho hL heps hepsrho heta.le
      hballA hballB hAb hBb hu J hnegative hs
  have hnz : ∀ s : I, 0 < (s : ℝ) → m s ≠ 0 := by
    intro s hs
    exact actualQuadraticSpectralMinimumTwo_ne_zero_of_boundary_positive μ hQK hKi e
      (hgeo s).1 (hgeo s).2.1.isPreconnected (hgeo s).2.2.2.1 ⟨0,(hgeo s).2.2.1⟩
      (hreg s) one_ne_zero
      (fun x hx => (hu s).2.2.2.1 x (hcl s (subset_closure hx)))
      (hpos s) heta (hnegative s hs) (hbd s hs)
  obtain ⟨s₀,hs₀,h₀⟩ := hanchor
  have hmpos := unitInterval_positive_of_positive_anchor_no_zero hm hnz hs₀ h₀
  intro t ht q hq hEq
  have hpositive : ∀ x ∈ closure (V t),
      0 < modifiedSigmaTwo e (fun j => Complex.I • e j) (fun y => u t y+q y) x := by
    intro x hx
    exact (hmpos t ht).trans_le (actualQuadraticSpectralMinimumTwo_le μ hQK hKi e
      (hgeo t).2.2.2.1 ⟨0,(hgeo t).2.2.1⟩
      (fun y hy => (hreg t y hy).of_le (by norm_num)) (hpos t) heta.le
      (hnegative t ht) hx hq hEq)
  refine ⟨hpositive,?_⟩
  apply strictConvexOn_power_of_modifiedSigmaTwo e (hgeo t).1 (hgeo t).2.1
    ((show ContDiffOn ℝ 2 (u t) (V t) from fun x hx =>
      ((hreg t x (subset_closure hx)).of_le (by norm_num)).contDiffWithinAt).add
        (IsQuadraticPolynomial_contDiff hq.1 2).contDiffOn)
    (fun x hx => hnegative t ht q hq hEq x (subset_closure hx))
    (fun x hx => (strictPsh_pluriharmonic_add_iff
      ((hreg t x (subset_closure hx)).of_le (by norm_num))
      (IsQuadraticPolynomial_contDiff hq.1 2).contDiffAt e (fun j => Complex.I • e j)
      (hq.2 x)).mpr (hpos t x (subset_closure hx)))
    (fun x hx => hpositive x (subset_closure hx))

end PowerConvexity
