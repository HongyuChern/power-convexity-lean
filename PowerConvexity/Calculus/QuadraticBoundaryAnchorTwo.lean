import PowerConvexity.Calculus.QuadraticJointSpectrumTwo
import PowerConvexity.Calculus.QuadraticL2Geometry
import PowerConvexity.Analysis.ParameterMinimum

/-! # A uniform interior anchor from positivity of all perturbations at a closure point

The closure here is the compact interior subdomain used in the proof, not the
original Dirichlet boundary. Actual C2-at-point regularity is stated explicitly.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set MeasureTheory
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
attribute [local irreducible] modifiedSigmaTwo modifiedK modifiedA modifiedB complexHessian pureHessian complexGradient
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem pluriharmonic_quadratic_family_interior_anchor_two
    (μ : Measure E) [IsFiniteMeasureOnCompacts μ] [Measure.IsOpenPosMeasure μ]
    {K : Set E} (hK : IsCompact K) (hKi : (interior K).Nonempty)
    (a b : Fin 2 → E) {U : Set E} {u : E → ℝ}
    (hu : ∀ x ∈ closure U, ContDiffAt ℝ 2 u x)
    (hpos : ∀ x ∈ closure U, (complexHessian a b u x).PosDef)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hneg : ∀ q : E → ℝ, IsPluriharmonicQuadratic a b q →
      quadraticL2Energy μ K q ≤ ε → ∀ x ∈ closure U, u x+q x < 0)
    {x₀ : E} (hx₀ : x₀ ∈ closure U)
    (hanchor : ∀ q : E → ℝ, IsPluriharmonicQuadratic a b q → quadraticL2Energy μ K q ≤ ε →
      0 < modifiedSigmaTwo a b (fun y => u y+q y) x₀) :
    ∃ x ∈ U, ∀ q : E → ℝ, IsPluriharmonicQuadratic a b q → quadraticL2Energy μ K q ≤ ε →
      0 < modifiedSigmaTwo a b (fun y => u y+q y) x := by
  letI := quadraticL2NormedAddCommGroup μ hK hKi
  letI : TopologicalSpace (quadraticSubmodule E) :=
    (quadraticL2NormedAddCommGroup μ hK hKi).toMetricSpace.toUniformSpace.toTopologicalSpace
  letI := quadraticL2InnerProductSpace μ hK hKi
  letI := quadraticSubmodule_finiteDimensional (E := E)
  let P := pluriharmonicQuadraticSubmodule a b
  let F : P →ₗ[ℝ] quadraticSubmodule E := P.subtype
  let S : Set P := {q | quadraticL2Energy μ K q.val.val ≤ ε}
  have hS : IsCompact S := pluriharmonicQuadraticL2Ball_isCompact μ hK hKi a b hε
  have hne : S.Nonempty := by
    refine ⟨0,?_⟩
    change quadraticL2Energy μ K (0 : E → ℝ) ≤ ε
    simpa [quadraticL2Energy] using hε
  have hclass (p : P) : IsPluriharmonicQuadratic a b (F p).val := ⟨p.val.property,p.property⟩
  have hF : ContinuousOn (fun z : E × P => modifiedSigmaTwo a b
      (fun y => u y+(F z.2).val y) z.1) (closure U ×ˢ S) := by
    intro z hz
    have hn := hneg _ (hclass z.2) hz.2 z.1 hz.1
    have hA := (strictPsh_pluriharmonic_add_iff (hu z.1 hz.1)
      (IsQuadraticPolynomial_contDiff (F z.2).property 2).contDiffAt a b ((hclass z.2).2 z.1)).mpr (hpos z.1 hz.1)
    exact (quadraticFamily_joint_modifiedSigmaTwo_continuousAt F a b (hu z.1 hz.1) hn
      (modifiedA_posDef a b hn hA)).continuousWithinAt
  have hp : 0 < compactLowerEnvelope S
      (fun y p => modifiedSigmaTwo a b (fun z => u z+(F p).val z) y) x₀ :=
    compactLowerEnvelope_pos_on (F := fun y p => modifiedSigmaTwo a b (fun z => u z+(F p).val z) y) hS hne hF hx₀ (fun p hp => hanchor _ (hclass p) hp)
  obtain ⟨x,hx,hxpos⟩ := exists_positive_anchor_of_closure
    (compactLowerEnvelope_continuousOn (F := fun y p => modifiedSigmaTwo a b (fun z => u z+(F p).val z) y) hS hF) hx₀ hp
  refine ⟨x,hx,?_⟩
  intro q hq hEq
  let p : P := ⟨⟨q,hq.1⟩,hq.2⟩
  exact hxpos.trans_le (compactLowerEnvelope_le_on (F := fun y p => modifiedSigmaTwo a b (fun z => u z+(F p).val z) y) hS hne hF (subset_closure hx)
    (show p ∈ S from hEq))

end PowerConvexity
