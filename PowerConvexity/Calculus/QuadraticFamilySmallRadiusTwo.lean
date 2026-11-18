import PowerConvexity.Analysis.CompactSmallParameterWithin
import PowerConvexity.Calculus.QuadraticPerturbedFamilyJets
import PowerConvexity.Calculus.QuadraticL2Geometry
import PowerConvexity.Calculus.SpectralHessianPositivityTwo

/-! # One L2 perturbation radius for a compact actual family

The family parameter includes the physical point. The only continuity inputs
are the physical point map and the unperturbed value, first jet and second jet.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set MeasureTheory
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
attribute [local irreducible] modifiedSigmaTwo modifiedK modifiedA modifiedB complexHessian pureHessian complexGradient
variable {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [InnerProductSpace ℝ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [TopologicalSpace P]

theorem exists_quadratic_L2_radius_negative_family
    (μ : Measure E) [IsFiniteMeasureOnCompacts μ] [Measure.IsOpenPosMeasure μ]
    {K : Set E} (hK : IsCompact K) (hKi : (interior K).Nonempty)
    {S : Set P} (hS : IsCompact S) (u : P → E → ℝ) (x : P → E)
    (hx : ContinuousOn x S) (hv : ContinuousOn (fun p => u p (x p)) S)
    (hneg : ∀ p ∈ S, u p (x p) < 0) :
    ∃ ε > 0, ∀ q : E → ℝ, IsQuadraticPolynomial q → quadraticL2Energy μ K q ≤ ε →
      ∀ p ∈ S, u p (x p)+q (x p) < 0 := by
  letI := quadraticL2NormedAddCommGroup μ hK hKi
  letI : TopologicalSpace (quadraticSubmodule E) :=
    (quadraticL2NormedAddCommGroup μ hK hKi).toMetricSpace.toUniformSpace.toTopologicalSpace
  letI := quadraticL2InnerProductSpace μ hK hKi
  letI := quadraticSubmodule_finiteDimensional (E := E)
  let F : quadraticSubmodule E →ₗ[ℝ] quadraticSubmodule E := LinearMap.id
  let V : quadraticSubmodule E × P → ℝ := fun z => u z.2 (x z.2)+(F z.1).val (x z.2)
  have hVc : ContinuousOn V (univ ×ˢ S) := quadraticPerturbedFamily_value_continuousOn F u x hx hv
  have hV0 (p : P) (hp : p ∈ S) : V (0,p) < 0 := by
    change u p (x p)+0 < 0
    simpa only [add_zero] using hneg p hp
  obtain ⟨r,hr,hh⟩ := compact_small_parameter_positive_within (F := fun z => -V z) hS
    (fun p hp => (hVc (0,p) ⟨mem_univ _,hp⟩).neg) (fun p hp => neg_pos.mpr (hV0 p hp))
  refine ⟨r^2,sq_pos_of_pos hr,?_⟩
  intro q hq hEq p hp
  let qP : quadraticSubmodule E := ⟨q,hq⟩
  have he : ‖qP‖^2 = quadraticL2Energy μ K q := quadraticL2_norm_sq μ hK hKi qP
  have hqP : ‖qP‖ ≤ r := by nlinarith [norm_nonneg qP]
  exact neg_pos.mp (hh qP hqP p hp)

theorem exists_quadratic_L2_radius_negative_and_positive_sigma_family_two
    (μ : Measure E) [IsFiniteMeasureOnCompacts μ] [Measure.IsOpenPosMeasure μ]
    {K : Set E} (hK : IsCompact K) (hKi : (interior K).Nonempty)
    (e : Module.Basis (Fin 2) ℂ E) {S : Set P} (hS : IsCompact S)
    (u : P → E → ℝ) (x : P → E)
    (hu : ∀ p ∈ S, ContDiffAt ℝ 2 (u p) (x p))
    (hx : ContinuousOn x S) (hv : ContinuousOn (fun p => u p (x p)) S)
    (hD : ContinuousOn (fun p => fderiv ℝ (u p) (x p)) S)
    (hH : ContinuousOn (fun p => realHessian (u p) (x p)) S)
    (hneg : ∀ p ∈ S, u p (x p) < 0)
    (hpos : ∀ p ∈ S, (complexHessian e (fun j => Complex.I • e j) (u p) (x p)).PosDef)
    (hσ : ∀ p ∈ S, 0 < modifiedSigmaTwo e (fun j => Complex.I • e j) (u p) (x p)) :
    ∃ ε > 0, ∀ q : E → ℝ, IsPluriharmonicQuadratic e (fun j => Complex.I • e j) q →
      quadraticL2Energy μ K q ≤ ε → ∀ p ∈ S, u p (x p)+q (x p) < 0 ∧
      0 < modifiedSigmaTwo e (fun j => Complex.I • e j) (fun y => u p y+q y) (x p) := by
  let a : Fin 2 → E := e
  let b : Fin 2 → E := fun j => Complex.I • e j
  letI := quadraticL2NormedAddCommGroup μ hK hKi
  letI : TopologicalSpace (quadraticSubmodule E) :=
    (quadraticL2NormedAddCommGroup μ hK hKi).toMetricSpace.toUniformSpace.toTopologicalSpace
  letI := quadraticL2InnerProductSpace μ hK hKi
  letI := quadraticSubmodule_finiteDimensional (E := E)
  let Q := pluriharmonicQuadraticSubmodule a b
  let F : Q →ₗ[ℝ] quadraticSubmodule E := Q.subtype
  let w : Q × P → E → ℝ := fun z y => u z.2 y+(F z.1).val y
  let X : Q × P → E := fun z => x z.2
  let V : Q × P → ℝ := fun z => w z (X z)
  let σ : Q × P → ℝ := fun z => modifiedSigmaTwo a b (w z) (X z)
  have hzpot (p : P) : w (0,p) = u p := by
    funext y
    change u p y+0 = u p y
    exact add_zero _
  have hreg (z : Q × P) (hz : z ∈ univ ×ˢ S) : ContDiffAt ℝ 2 (w z) (X z) :=
    (hu z.2 hz.2).add (IsQuadraticPolynomial_contDiff (F z.1).property 2).contDiffAt
  have hVc : ContinuousOn V (univ ×ˢ S) := quadraticPerturbedFamily_value_continuousOn F u x hx hv
  have hDc : ContinuousOn (fun z => fderiv ℝ (w z) (X z)) (univ ×ˢ S) :=
    quadraticPerturbedFamily_fderiv_continuousOn F u x hu hx hD
  have hHc : ContinuousOn (fun z => realHessian (w z) (X z)) (univ ×ˢ S) :=
    quadraticPerturbedFamily_realHessian_continuousOn F u x hu hx hH
  have hσc (p : P) (hp : p ∈ S) : ContinuousWithinAt σ (univ ×ˢ S) (0,p) := by
    apply actualFamily_modifiedSigmaTwo_continuousWithinAt_of_jets a b w X hreg hVc hDc hHc
      (show (0,p) ∈ univ ×ˢ S from ⟨mem_univ _,hp⟩)
    · change w (0,p) (x p) < 0
      rw [hzpot]
      exact hneg p hp
    · change (complexHessian a b (w (0,p)) (x p)).PosDef
      rw [hzpot]
      exact hpos p hp
  have hV0 (p : P) (hp : p ∈ S) : V (0,p) < 0 := by
    change w (0,p) (x p) < 0
    rw [hzpot]
    exact hneg p hp
  have hσ0 (p : P) (hp : p ∈ S) : 0 < σ (0,p) := by
    change 0 < modifiedSigmaTwo a b (w (0,p)) (x p)
    rw [hzpot]
    exact hσ p hp
  obtain ⟨r,hr,hh⟩ := compact_small_parameter_pair_within hS
    (fun p hp => hVc (0,p) ⟨mem_univ _,hp⟩) hσc hV0 hσ0
  refine ⟨r^2,sq_pos_of_pos hr,?_⟩
  intro q hq hEq p hp
  let qP : Q := ⟨⟨q,hq.1⟩,hq.2⟩
  have he : ‖qP‖^2 = quadraticL2Energy μ K q := quadraticL2_norm_sq μ hK hKi qP.val
  have hqP : ‖qP‖ ≤ r := by nlinarith [norm_nonneg qP]
  exact hh qP hqP p hp

end PowerConvexity
