import PowerConvexity.Analysis.CompactSmallParameter
import PowerConvexity.Calculus.QuadraticJointSpectrumTwo
import PowerConvexity.Calculus.QuadraticL2Geometry
import PowerConvexity.Calculus.SpectralHessianPositivityTwo

/-! # One actual L2 perturbation radius on a compact strict region -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set MeasureTheory
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
attribute [local irreducible] modifiedSigmaTwo modifiedK modifiedA modifiedB complexHessian pureHessian complexGradient
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [InnerProductSpace ℝ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem exists_quadratic_L2_radius_negative_and_positive_sigma_two
    (μ : Measure E) [IsFiniteMeasureOnCompacts μ] [Measure.IsOpenPosMeasure μ]
    {K X : Set E} (hK : IsCompact K) (hKi : (interior K).Nonempty) (hX : IsCompact X)
    (e : Module.Basis (Fin 2) ℂ E) {u : E → ℝ}
    (hu : ∀ x ∈ X, ContDiffAt ℝ 2 u x) (hneg : ∀ x ∈ X, u x < 0)
    (hpos : ∀ x ∈ X, (complexHessian e (fun j => Complex.I • e j) u x).PosDef)
    (hσ : ∀ x ∈ X, 0 < modifiedSigmaTwo e (fun j => Complex.I • e j) u x) :
    ∃ ε > 0, ∀ q : E → ℝ, IsPluriharmonicQuadratic e (fun j => Complex.I • e j) q →
      quadraticL2Energy μ K q ≤ ε → ∀ x ∈ X, u x+q x < 0 ∧
      0 < modifiedSigmaTwo e (fun j => Complex.I • e j) (fun y => u y+q y) x := by
  let a : Fin 2 → E := e
  let b : Fin 2 → E := fun j => Complex.I • e j
  letI := quadraticL2NormedAddCommGroup μ hK hKi
  letI : TopologicalSpace (quadraticSubmodule E) :=
    (quadraticL2NormedAddCommGroup μ hK hKi).toMetricSpace.toUniformSpace.toTopologicalSpace
  letI := quadraticL2InnerProductSpace μ hK hKi
  letI := quadraticSubmodule_finiteDimensional (E := E)
  let P := pluriharmonicQuadraticSubmodule a b
  let F : P →ₗ[ℝ] quadraticSubmodule E := P.subtype
  let V : P × E → ℝ := fun z => u z.2+(F z.1).val z.2
  let S : P × E → ℝ := fun z => modifiedSigmaTwo a b (fun y => u y+(F z.1).val y) z.2
  have hzpot : (fun y => u y+(F 0).val y) = u := by
    funext y
    change u y+0 = u y
    exact add_zero _
  have hVc (x : E) (hx : x ∈ X) : ContinuousAt V (0,x) := by
    have hh : ContinuousAt (fun z : E × P => u z.1+(F z.2).val z.1) (x,0) :=
      ((hu x hx).continuousAt.comp (continuousAt_fst (p := (x,0)))).add
        (quadraticFamily_joint_value_contDiff F 0).continuous.continuousAt
    exact hh.comp (f := Prod.swap) (x := (0,x)) continuous_swap.continuousAt
  have hSc (x : E) (hx : x ∈ X) : ContinuousAt S (0,x) := by
    have hn : u x+(F 0).val x < 0 := by change u x+0 < 0; simpa only [add_zero] using hneg x hx
    have hA : (modifiedA a b (fun y => u y+(F 0).val y) x).PosDef := by
      rw [hzpot]
      exact modifiedA_posDef a b (hneg x hx) (hpos x hx)
    have hh := quadraticFamily_joint_modifiedSigmaTwo_continuousAt F a b (hu x hx) hn hA
    exact hh.comp (f := Prod.swap) (x := (0,x)) continuous_swap.continuousAt
  have hV0 (x : E) (hx : x ∈ X) : V (0,x) < 0 := by
    change u x+0 < 0
    simpa only [add_zero] using hneg x hx
  have hS0 (x : E) (hx : x ∈ X) : 0 < S (0,x) := by
    change 0 < modifiedSigmaTwo a b (fun y => u y+(F 0).val y) x
    rw [hzpot]
    exact hσ x hx
  obtain ⟨r,hr,hh⟩ := compact_small_parameter_pair hX hVc hSc hV0 hS0
  refine ⟨r^2,sq_pos_of_pos hr,?_⟩
  intro q hq hEq x hx
  let p : P := ⟨⟨q,hq.1⟩,hq.2⟩
  have he : ‖p‖^2 = quadraticL2Energy μ K q := quadraticL2_norm_sq μ hK hKi p.val
  have hp : ‖p‖ ≤ r := by nlinarith [norm_nonneg p]
  exact hh p hp x hx

end PowerConvexity
