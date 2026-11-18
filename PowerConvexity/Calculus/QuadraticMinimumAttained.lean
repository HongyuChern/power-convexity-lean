import PowerConvexity.Calculus.QuadraticL2Geometry
import PowerConvexity.Calculus.QuadraticModifiedParameter

/-! # Attainment of the actual lowest Schur root on the actual L2 ball -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem exists_quadraticFamily_minimizer_on_compact
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (F : P →ₗ[ℝ] quadraticSubmodule E) (a b : Fin 2 → E)
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x)
    {S : Set P} (hS : IsCompact S) (hne : S.Nonempty)
    (hneg : ∀ p ∈ S, u x+(F p).val x < 0)
    (hpos : ∀ p ∈ S, (modifiedA a b (fun y => u y+(F p).val y) x).PosDef) :
    ∃ p ∈ S, ∀ r ∈ S,
      modifiedSigmaTwo a b (fun y => u y+(F p).val y) x ≤
        modifiedSigmaTwo a b (fun y => u y+(F r).val y) x := by
  apply IsCompact.exists_isMinOn (f := fun p => modifiedSigmaTwo a b
    (fun y => u y+(F p).val y) x) hS hne
  intro p hp
  exact (quadraticFamily_modifiedSigmaTwo_continuousAt F a b hu
    (hneg p hp) (hpos p hp)).continuousWithinAt

theorem exists_pluriharmonic_quadratic_minimizer
    (μ : Measure E) [IsFiniteMeasureOnCompacts μ] [Measure.IsOpenPosMeasure μ]
    {K : Set E} (hK : IsCompact K) (hKi : (interior K).Nonempty)
    (a b : Fin 2 → E) {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hneg : ∀ q : E → ℝ, IsPluriharmonicQuadratic a b q → quadraticL2Energy μ K q ≤ ε → u x+q x < 0)
    (hpos : ∀ q : E → ℝ, IsPluriharmonicQuadratic a b q → quadraticL2Energy μ K q ≤ ε →
      (modifiedA a b (fun y => u y+q y) x).PosDef) :
    ∃ q : E → ℝ, IsPluriharmonicQuadratic a b q ∧ quadraticL2Energy μ K q ≤ ε ∧
      ∀ h : E → ℝ, IsPluriharmonicQuadratic a b h → quadraticL2Energy μ K h ≤ ε →
        modifiedSigmaTwo a b (fun y => u y+q y) x ≤
          modifiedSigmaTwo a b (fun y => u y+h y) x := by
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
  obtain ⟨q,hq,hmin⟩ := exists_quadraticFamily_minimizer_on_compact F a b hu hS hne
    (fun p hp => hneg _ ⟨p.val.property,p.property⟩ hp)
    (fun p hp => hpos _ ⟨p.val.property,p.property⟩ hp)
  refine ⟨q.val.val,⟨q.val.property,q.property⟩,hq,?_⟩
  intro h hh hE
  let r : P := ⟨⟨h,hh.1⟩,hh.2⟩
  exact hmin r (show r ∈ S from hE)

end PowerConvexity
