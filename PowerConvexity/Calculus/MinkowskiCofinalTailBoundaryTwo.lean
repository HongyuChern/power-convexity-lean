import PowerConvexity.Calculus.ActualNearBallCommonSpectrumTwo
import PowerConvexity.Calculus.MinkowskiCofinalTruncationExhaustionTwo

/-! # Actual near-ball cutoffs with the thickness quantifier kept outside

For each genuine positive distance truncation we construct its own positive
near-ball time from the already proved actual spectral margin.  The remaining
boundary premise is then only on the matching tail of the parameter interval.
A cofinal collection of such matched tails is enough to exhaust the original
domains.  No single near-ball time valid as the thickness tends to zero is
asserted, and no positivity of the remaining tails is assumed implicitly.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
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

theorem minkowski_actual_near_ball_cutoffs_and_cofinal_tail_exhaustion_two
    (μ : Measure E) [IsFiniteMeasureOnCompacts μ] [Measure.IsOpenPosMeasure μ]
    {K : Set E} (hQK : IsCompact K) (hKi : (interior K).Nonempty)
    {A : Set E} (hA : IsOpen A) (hconv : Convex ℝ A) (hK : IsCompact (closure A))
    (hboundary : HasSmoothLocalDefiningFunction A)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {R ρ L : ℝ} (hR : 0 < R) (hρ : 0 < ρ) (hL : 0 ≤ L)
    (hballA : closedBall (0 : E) ρ ⊆ A) (hballB : closedBall (0 : E) ρ ⊆ ball 0 R)
    (hAb : ∀ x ∈ A, ‖x‖ ≤ L) (hBb : ∀ x ∈ ball (0 : E) R, ‖x‖ ≤ L)
    {u : I → E → ℝ}
    (hu : ClassicalMinkowskiFamilyTwo e (fun j => Complex.I • e j) A (ball 0 R) u)
    (J : ∀ t, ClosureC2Jet (u t) (minkowskiDomain t A (ball 0 R))) :
    ∃ τ : Ioo (0 : ℝ) ρ → ℝ,
      (∀ ε : Ioo (0 : ℝ) ρ, 0 < τ ε ∧ τ ε ≤ (1/2 : ℝ) ∧
        ∀ t : I, (t : ℝ) ≤ τ ε →
          ∀ x ∈ closure (distanceInteriorDomain (minkowskiDomain t A (ball 0 R)) ε),
            0 < modifiedSigmaTwo e (fun j => Complex.I • e j) (u t) x) ∧
      ((∀ d : ℝ, 0 < d → ∃ ε : Ioo (0 : ℝ) ρ, (ε : ℝ) < d ∧
          ∀ t : I, τ ε < (t : ℝ) →
            ∀ x ∈ frontier (distanceInteriorDomain (minkowskiDomain t A (ball 0 R)) ε),
              0 < modifiedSigmaTwo e (fun j => Complex.I • e j) (u t) x) →
        ∀ t : I,
          (∀ x ∈ minkowskiDomain t A (ball 0 R),
            0 < modifiedSigmaTwo e (fun j => Complex.I • e j) (u t) x) ∧
          StrictConvexOn ℝ (minkowskiDomain t A (ball 0 R)) (powerTransform (u t))) := by
  have hcut (ε : Ioo (0 : ℝ) ρ) : ∃ τ > 0, τ ≤ (1/2 : ℝ) ∧
      ∀ t : I, (t : ℝ) ≤ τ →
        ∀ x ∈ closure (distanceInteriorDomain (minkowskiDomain t A (ball 0 R)) ε),
          0 < modifiedSigmaTwo e (fun j => Complex.I • e j) (u t) x := by
    obtain ⟨η,hη,τ,hτ,hτhalf,κ,hκ,_,hmargin⟩ :=
      minkowski_actual_common_spectral_margin_near_ball_two μ hQK hKi
        hA hconv hK hboundary e hab hR hρ hL ε.property.1 ε.property.2
        hballA hballB hAb hBb hu J
    refine ⟨τ,hτ,hτhalf,?_⟩
    intro t ht x hx
    have hzero : IsPluriharmonicQuadratic e (fun j => Complex.I • e j) (fun _ : E => 0) :=
      ⟨(quadraticSubmodule E).zero_mem,
        (pluriharmonicQuadraticSubmodule e (fun j => Complex.I • e j)).zero_mem⟩
    have he0 : quadraticL2Energy μ K (fun _ : E => 0) ≤ η := by
      simpa [quadraticL2Energy] using hη.le
    have hm := hmargin t ht (fun _ : E => 0) hzero he0 x hx
    simpa only [add_zero] using hκ.trans_le hm
  choose τ hτ hτhalf hnear using hcut
  refine ⟨τ,fun ε => ⟨hτ ε,hτhalf ε,hnear ε⟩,?_⟩
  intro htail
  apply minkowski_actual_exhaustion_from_cofinal_truncation_boundary_two
    μ hQK hKi e hab hA hconv hK hboundary hR hρ hL hballA hballB hAb hBb hu J
  intro d hd
  obtain ⟨ε,hεd,hfar⟩ := htail d hd
  refine ⟨ε,ε.property.1,hεd,?_⟩
  intro t x hx
  by_cases ht : (t : ℝ) ≤ τ ε
  · exact hnear ε t ht x (frontier_subset_closure hx)
  · exact hfar t (lt_of_not_ge ht) x hx

end PowerConvexity
