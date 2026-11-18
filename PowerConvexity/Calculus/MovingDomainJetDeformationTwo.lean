import PowerConvexity.Calculus.MovingDomainDeformationTwo
import PowerConvexity.Calculus.ActualJetSpectrumContinuityTwo

/-! # Moving-domain continuation from actual spatial two-jet continuity -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set MeasureTheory
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
attribute [local irreducible] modifiedSigmaTwo modifiedK modifiedA modifiedB complexHessian pureHessian complexGradient
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [InnerProductSpace ℝ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [ProperSpace E] [Nontrivial E]

theorem constantDensity_quadratic_moving_deformation_of_jets_two
    (μ : Measure E) [IsFiniteMeasureOnCompacts μ] [Measure.IsOpenPosMeasure μ]
    {K : Set E} (hK : IsCompact K) (hKi : (interior K).Nonempty)
    (e : Module.Basis (Fin 2) ℂ E)
    {U : Set E} (hU : IsOpen U) (hconn : IsPreconnected U)
    (hCU : IsCompact (closure U)) (hneU : U.Nonempty)
    (φ : ℝ → E ≃ₜ E) (u : ℝ → E → ℝ) (ρ : ℝ → ℂ)
    (hu : ∀ t ∈ Icc (0:ℝ) 1, ∀ x ∈ closure (φ t '' U), ContDiffAt ℝ 4 (u t) x)
    (hρ : ∀ t ∈ Icc (0:ℝ) 1, ρ t ≠ 0)
    (hdet : ∀ t ∈ Icc (0:ℝ) 1, ∀ x ∈ φ t '' U,
      (complexHessian e (fun j => Complex.I • e j) (u t) x).det = ρ t)
    (hpos : ∀ t ∈ Icc (0:ℝ) 1, ∀ x ∈ closure (φ t '' U),
      (complexHessian e (fun j => Complex.I • e j) (u t) x).PosDef)
    {ε : ℝ} (hε : 0 < ε)
    (hneg : ∀ t ∈ Icc (0:ℝ) 1, ∀ q : E → ℝ,
      IsPluriharmonicQuadratic e (fun j => Complex.I • e j) q →
      quadraticL2Energy μ K q ≤ ε → ∀ x ∈ closure (φ t '' U), u t x+q x < 0)
    (h0 : ∀ x ∈ closure (φ 0 '' U),
      0 < modifiedSigmaTwo e (fun j => Complex.I • e j) (u 0) x)
    (hbd : ∀ t ∈ Icc (0:ℝ) 1, ∀ q : E → ℝ,
      IsPluriharmonicQuadratic e (fun j => Complex.I • e j) q →
      quadraticL2Energy μ K q ≤ ε → ∀ x ∈ frontier (φ t '' U),
      0 < modifiedSigmaTwo e (fun j => Complex.I • e j) (fun y => u t y+q y) x)
    (hjets :
      letI := quadraticL2NormedAddCommGroup μ hK hKi
      letI : TopologicalSpace (quadraticSubmodule E) :=
        (quadraticL2NormedAddCommGroup μ hK hKi).toMetricSpace.toUniformSpace.toTopologicalSpace
      let P := pluriharmonicQuadraticSubmodule e (fun j => Complex.I • e j)
      let S := Icc (0:ℝ) 1 ×ˢ (closure U ×ˢ {q : P | quadraticL2Energy μ K q.val.val ≤ ε})
      ContinuousOn (fun z : ℝ × (E × P) => u z.1 (φ z.1 z.2.1)+z.2.2.val.val (φ z.1 z.2.1)) S ∧
      ContinuousOn (fun z : ℝ × (E × P) =>
        fderiv ℝ (fun y => u z.1 y+z.2.2.val.val y) (φ z.1 z.2.1)) S ∧
      ContinuousOn (fun z : ℝ × (E × P) =>
        realHessian (fun y => u z.1 y+z.2.2.val.val y) (φ z.1 z.2.1)) S) :
    ∀ t ∈ Icc (0:ℝ) 1, ∀ q : E → ℝ,
      IsPluriharmonicQuadratic e (fun j => Complex.I • e j) q →
      quadraticL2Energy μ K q ≤ ε → ∀ x ∈ closure (φ t '' U),
      0 < modifiedSigmaTwo e (fun j => Complex.I • e j) (fun y => u t y+q y) x := by
  apply constantDensity_quadratic_moving_deformation_two μ hK hKi e hU hconn hCU hneU
    φ u ρ hu hρ hdet hpos hε hneg h0 hbd
  letI := quadraticL2NormedAddCommGroup μ hK hKi
  letI : TopologicalSpace (quadraticSubmodule E) :=
    (quadraticL2NormedAddCommGroup μ hK hKi).toMetricSpace.toUniformSpace.toTopologicalSpace
  let P := pluriharmonicQuadraticSubmodule e (fun j => Complex.I • e j)
  let S := Icc (0:ℝ) 1 ×ˢ (closure U ×ˢ {q : P | quadraticL2Energy μ K q.val.val ≤ ε})
  let w : ℝ × (E × P) → E → ℝ := fun z y => u z.1 y+z.2.2.val.val y
  let X : ℝ × (E × P) → E := fun z => φ z.1 z.2.1
  have hj : ContinuousOn (fun z => w z (X z)) S ∧
      ContinuousOn (fun z => fderiv ℝ (w z) (X z)) S ∧
      ContinuousOn (fun z => realHessian (w z) (X z)) S := hjets
  have hcl (z : ℝ × (E × P)) (hz : z ∈ S) : X z ∈ closure (φ z.1 '' U) := by
    rw [← (φ z.1).image_closure]
    exact ⟨z.2.1,hz.2.1,rfl⟩
  have hclass (z : ℝ × (E × P)) :
      IsPluriharmonicQuadratic e (fun j => Complex.I • e j) z.2.2.val.val :=
    ⟨z.2.2.val.property,z.2.2.property⟩
  have hreg (z : ℝ × (E × P)) (hz : z ∈ S) : ContDiffAt ℝ 2 (w z) (X z) :=
    ((hu z.1 hz.1 (X z) (hcl z hz)).of_le (by norm_num)).add
      (IsQuadraticPolynomial_contDiff (hclass z).1 2).contDiffAt
  apply actualFamily_modifiedSigmaTwo_continuousOn_of_jets e (fun j => Complex.I • e j)
    w X hreg hj.1 hj.2.1 hj.2.2
  · intro z hz
    exact hneg z.1 hz.1 _ (hclass z) hz.2.2 (X z) (hcl z hz)
  · intro z hz
    exact (strictPsh_pluriharmonic_add_iff
      ((hu z.1 hz.1 (X z) (hcl z hz)).of_le (by norm_num))
      (IsQuadraticPolynomial_contDiff (hclass z).1 2).contDiffAt e
      (fun j => Complex.I • e j) ((hclass z).2 (X z))).mpr
        (hpos z.1 hz.1 (X z) (hcl z hz))

end PowerConvexity
