import PowerConvexity.Calculus.MinkowskiActualDeformationFromCollarTwo

/-! A checked downstream use of the exact geometric boundary premise. The
actual classical family and the common truncated-boundary spectral positivity
are explicit inputs, as in the cumulative baseline. -/

open Set Metric MeasureTheory
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  [FiniteDimensional ℂ E] [Nontrivial E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]

local notation "I" => Icc (0 : ℝ) 1

theorem c112_resume_actual_truncation_strict_of_boundary_sigma
    (μ : Measure E) [IsFiniteMeasureOnCompacts μ] [Measure.IsOpenPosMeasure μ]
    {K : Set E} (hK : IsCompact K) (hKi : (interior K).Nonempty)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {A : Set E} (hAo : IsOpen A) (hA : Convex ℝ A)
    (hAK : IsCompact (closure A)) (hSmooth : HasSmoothLocalDefiningFunction A)
    {R ρ L ε : ℝ} (hR : 0 < R) (hρ : 0 < ρ) (hL : 0 ≤ L) (hε : 0 < ε) (hερ : ε < ρ)
    (hballA : closedBall (0 : E) ρ ⊆ A) (hballB : closedBall (0 : E) ρ ⊆ ball 0 R)
    (hAb : ∀ x ∈ A, ‖x‖ ≤ L) (hBb : ∀ x ∈ ball (0 : E) R, ‖x‖ ≤ L)
    {u : I → E → ℝ}
    (hu : ClassicalMinkowskiFamilyTwo e (fun j => Complex.I • e j) A (ball 0 R) u)
    (J : ∀ t, ClosureC2Jet (u t) (minkowskiDomain t A (ball 0 R)))
    (hboundary : ∀ t : I, ∀ x ∈ frontier (distanceInteriorDomain (minkowskiDomain t A (ball 0 R)) ε),
      0 < modifiedSigmaTwo e (fun j => Complex.I • e j) (u t) x) :
    ∀ t : I, StrictConvexOn ℝ (distanceInteriorDomain (minkowskiDomain t A (ball 0 R)) ε)
      (powerTransform (u t)) := by
  obtain ⟨η, hη, hstrict⟩ := minkowski_actual_deformation_from_actual_boundary_sigma_two
    μ hK hKi e hab hAo hA hAK hSmooth hR hρ hL hε hερ hballA hballB hAb hBb hu J hboundary
  intro t
  have hq : IsPluriharmonicQuadratic e (fun j => Complex.I • e j) (fun _ : E => 0) :=
    ⟨(quadraticSubmodule E).zero_mem,
      (pluriharmonicQuadraticSubmodule e (fun j => Complex.I • e j)).zero_mem⟩
  have henergy : quadraticL2Energy μ K (fun _ : E => 0) ≤ η := by
    simpa [quadraticL2Energy] using hη.le
  simpa only [add_zero] using (hstrict t (fun _ => 0) hq henergy).2

end PowerConvexity
