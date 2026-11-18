import PowerConvexity.Calculus.MinkowskiActualCommonBoundaryRadiusTwo
import PowerConvexity.Calculus.MinkowskiActualDeformationTwo

/-! # Actual deformation after the zero-parameter control is proved.
The only remaining analytic inputs here are the actual classical family and
unperturbed boundary spectral positivity on the actual common truncation.
The same actual L2 radius, domains and minimum are used throughout; the
strictly convex object is exactly -sqrt(-u-q).
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

theorem minkowski_actual_deformation_from_actual_boundary_sigma_two
    (μ : Measure E) [IsFiniteMeasureOnCompacts μ] [Measure.IsOpenPosMeasure μ]
    {K : Set E} (hK : IsCompact K) (hKi : (interior K).Nonempty)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {A : Set E} (hAo : IsOpen A) (hA : Convex ℝ A)
    (hAK : IsCompact (closure A)) (hSmooth : HasSmoothLocalDefiningFunction A) {R ρ L ε : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) (hL : 0 ≤ L) (hε : 0 < ε) (hερ : ε < ρ)
    (hballA : closedBall (0 : E) ρ ⊆ A) (hballB : closedBall (0 : E) ρ ⊆ ball 0 R)
    (hAb : ∀ x ∈ A, ‖x‖ ≤ L) (hBb : ∀ x ∈ ball (0 : E) R, ‖x‖ ≤ L)
    {u : I → E → ℝ}
    (hu : ClassicalMinkowskiFamilyTwo e (fun j => Complex.I • e j) A (ball 0 R) u)
    (J : ∀ t, ClosureC2Jet (u t) (minkowskiDomain t A (ball 0 R)))
    (hboundary : ∀ t : I, ∀ x ∈ frontier (distanceInteriorDomain (minkowskiDomain t A (ball 0 R)) ε),
      0 < modifiedSigmaTwo e (fun j => Complex.I • e j) (u t) x) :
    ∃ η > 0, ∀ t : I, ∀ q : E → ℝ,
      IsPluriharmonicQuadratic e (fun j => Complex.I • e j) q →
      quadraticL2Energy μ K q ≤ η →
      (∀ x ∈ closure (distanceInteriorDomain (minkowskiDomain t A (ball 0 R)) ε),
        0 < modifiedSigmaTwo e (fun j => Complex.I • e j) (fun y => u t y+q y) x) ∧
      StrictConvexOn ℝ (distanceInteriorDomain (minkowskiDomain t A (ball 0 R)) ε)
        (powerTransform (fun y => u t y+q y)) := by
  let V : I → Set E := fun t => distanceInteriorDomain (minkowskiDomain t A (ball 0 R)) ε
  have hgeo (t : I) := minkowski_distanceInterior_uniform_geometry hAo isOpen_ball
    hA (convex_ball 0 R) hρ hε hερ hballA hballB hAb hBb t
  have hAn : A.Nonempty := ⟨0,hballA (mem_closedBall_self hρ.le)⟩
  have hU (t : I) : IsOpen (minkowskiDomain t A (ball 0 R)) :=
    minkowskiDomain_isOpen hAo isOpen_ball hAn t
  have hcl (t : I) : closure (V t) ⊆ minkowskiDomain t A (ball 0 R) := (hgeo t).2.2.2.2
  obtain ⟨η,hη,hnegative,hbd,hm⟩ := minkowski_actual_exists_common_boundary_radius_two
    μ hK hKi e hab hAo hA hAK hSmooth hR hρ hL hε hερ
    hballA hballB hAb hBb hu J hboundary
  refine ⟨η,hη,?_⟩
  apply constantDensity_quadratic_actual_domain_deformation_two μ hK hKi e
    (V := V) (fun t => (hgeo t).1) (fun t => (hgeo t).2.1)
    (fun t => (hgeo t).2.2.2.1) (fun t => ⟨0,(hgeo t).2.2.1⟩)
    u (fun _ => 1)
    (fun t x hx => (hu t).1.contDiffAt ((hU t).mem_nhds (hcl t hx)))
    (fun _ => one_ne_zero)
    (fun t x hx => (hu t).2.2.2.1 x (hcl t (subset_closure hx)))
    (fun t x hx => (hu t).2.2.1 x (hcl t hx)) hη hnegative
    ⟨0,by norm_num⟩ ?_ hbd hm
  intro x hx
  apply hu.ball_endpoint_sigma_positive e hab hAn hR
  have hxU := hcl ⟨0,by norm_num⟩ hx
  simpa only [minkowskiDomain_zero hAn] using hxU

end PowerConvexity
