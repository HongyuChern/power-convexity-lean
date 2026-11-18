import PowerConvexity.Calculus.QuadraticSpace
import PowerConvexity.Calculus.QuadraticEnergyDefinite
import PowerConvexity.Calculus.QuadraticEnergyPaths
import Mathlib.Analysis.InnerProductSpace.Defs

/-! # Actual L2 geometry and compact balls of quadratic perturbations -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Metric
open scoped Topology
namespace PowerConvexity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

@[instance_reducible]
noncomputable def quadraticL2Core (μ : Measure E)
    [IsFiniteMeasureOnCompacts μ] [Measure.IsOpenPosMeasure μ]
    {K : Set E} (hK : IsCompact K) (hKi : (interior K).Nonempty) :
    InnerProductSpace.Core ℝ (quadraticSubmodule E) where
  inner q h := quadraticL2Pairing μ K q.val h.val
  conj_inner_symm q h := by
    change (∫ y in K, h.val y*q.val y ∂μ) = ∫ y in K, q.val y*h.val y ∂μ
    congr 1
    funext y
    exact mul_comm _ _
  re_inner_nonneg q := by
    change 0 ≤ ∫ y in K, q.val y*q.val y ∂μ
    exact integral_nonneg fun y => mul_self_nonneg _
  add_left q h k := by
    change (∫ y in K, (q.val y+h.val y)*k.val y ∂μ) =
      (∫ y in K, q.val y*k.val y ∂μ)+(∫ y in K, h.val y*k.val y ∂μ)
    simp_rw [add_mul]
    apply integral_add
    · exact ((IsQuadraticPolynomial_contDiff q.property 0).continuous.continuousOn.mul
        (IsQuadraticPolynomial_contDiff k.property 0).continuous.continuousOn).integrableOn_compact hK
    · exact ((IsQuadraticPolynomial_contDiff h.property 0).continuous.continuousOn.mul
        (IsQuadraticPolynomial_contDiff k.property 0).continuous.continuousOn).integrableOn_compact hK
  smul_left q h r := by
    change (∫ y in K, (r*q.val y)*h.val y ∂μ) = r*(∫ y in K, q.val y*h.val y ∂μ)
    simp_rw [mul_assoc]
    exact integral_const_mul _ _
  definite q h := by
    apply Subtype.ext
    apply (quadraticL2Energy_eq_zero_iff μ hK hKi q.property).mp
    simpa only [quadraticL2Energy,quadraticL2Pairing,pow_two] using h

@[instance_reducible]
noncomputable def quadraticL2NormedAddCommGroup (μ : Measure E)
    [IsFiniteMeasureOnCompacts μ] [Measure.IsOpenPosMeasure μ]
    {K : Set E} (hK : IsCompact K) (hKi : (interior K).Nonempty) :
    NormedAddCommGroup (quadraticSubmodule E) := by
  letI := quadraticL2Core μ hK hKi
  exact InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)

@[instance_reducible]
noncomputable def quadraticL2InnerProductSpace (μ : Measure E)
    [IsFiniteMeasureOnCompacts μ] [Measure.IsOpenPosMeasure μ]
    {K : Set E} (hK : IsCompact K) (hKi : (interior K).Nonempty) :
    letI := quadraticL2NormedAddCommGroup μ hK hKi
    letI : TopologicalSpace (quadraticSubmodule E) :=
      (quadraticL2NormedAddCommGroup μ hK hKi).toMetricSpace.toUniformSpace.toTopologicalSpace
    InnerProductSpace ℝ (quadraticSubmodule E) := by
  letI := quadraticL2Core μ hK hKi
  exact InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℝ (quadraticSubmodule E))

section Geometry
variable (μ : Measure E) [IsFiniteMeasureOnCompacts μ] [Measure.IsOpenPosMeasure μ]
  {K : Set E} (hK : IsCompact K) (hKi : (interior K).Nonempty)

theorem quadraticL2_norm_sq (q : quadraticSubmodule E) :
    letI := quadraticL2NormedAddCommGroup μ hK hKi
    letI : TopologicalSpace (quadraticSubmodule E) :=
      (quadraticL2NormedAddCommGroup μ hK hKi).toMetricSpace.toUniformSpace.toTopologicalSpace
    ‖q‖^2 = quadraticL2Energy μ K q.val := by
  letI := quadraticL2NormedAddCommGroup μ hK hKi
  letI : TopologicalSpace (quadraticSubmodule E) :=
    (quadraticL2NormedAddCommGroup μ hK hKi).toMetricSpace.toUniformSpace.toTopologicalSpace
  letI := quadraticL2InnerProductSpace μ hK hKi
  rw [← real_inner_self_eq_norm_sq]
  change (∫ y in K, q.val y*q.val y ∂μ) = ∫ y in K, (q.val y)^2 ∂μ
  simp only [pow_two]

theorem quadraticL2Ball_eq_closedBall {ε : ℝ} (hε : 0 ≤ ε) :
    letI := quadraticL2NormedAddCommGroup μ hK hKi
    letI : TopologicalSpace (quadraticSubmodule E) :=
      (quadraticL2NormedAddCommGroup μ hK hKi).toMetricSpace.toUniformSpace.toTopologicalSpace
    {q : quadraticSubmodule E | quadraticL2Energy μ K q.val ≤ ε} =
      closedBall 0 (Real.sqrt ε) := by
  letI := quadraticL2NormedAddCommGroup μ hK hKi
  letI : TopologicalSpace (quadraticSubmodule E) :=
    (quadraticL2NormedAddCommGroup μ hK hKi).toMetricSpace.toUniformSpace.toTopologicalSpace
  letI := quadraticL2InnerProductSpace μ hK hKi
  ext q
  rw [mem_setOf_eq,mem_closedBall,dist_zero_right,← quadraticL2_norm_sq μ hK hKi]
  exact (Real.le_sqrt (norm_nonneg q) hε).symm

theorem quadraticL2Ball_isCompact [FiniteDimensional ℝ E] {ε : ℝ} (hε : 0 ≤ ε) :
    letI := quadraticL2NormedAddCommGroup μ hK hKi
    letI : TopologicalSpace (quadraticSubmodule E) :=
      (quadraticL2NormedAddCommGroup μ hK hKi).toMetricSpace.toUniformSpace.toTopologicalSpace
    IsCompact {q : quadraticSubmodule E | quadraticL2Energy μ K q.val ≤ ε} := by
  letI := quadraticL2NormedAddCommGroup μ hK hKi
  letI : TopologicalSpace (quadraticSubmodule E) :=
    (quadraticL2NormedAddCommGroup μ hK hKi).toMetricSpace.toUniformSpace.toTopologicalSpace
  letI := quadraticL2InnerProductSpace μ hK hKi
  letI := quadraticSubmodule_finiteDimensional (E := E)
  rw [quadraticL2Ball_eq_closedBall μ hK hKi hε]
  exact isCompact_closedBall _ _

theorem quadraticL2Jet_continuous [FiniteDimensional ℝ E] :
    letI := quadraticL2NormedAddCommGroup μ hK hKi
    letI : TopologicalSpace (quadraticSubmodule E) :=
      (quadraticL2NormedAddCommGroup μ hK hKi).toMetricSpace.toUniformSpace.toTopologicalSpace
    Continuous (quadraticJetMap (E := E)) := by
  letI := quadraticL2NormedAddCommGroup μ hK hKi
  letI : TopologicalSpace (quadraticSubmodule E) :=
    (quadraticL2NormedAddCommGroup μ hK hKi).toMetricSpace.toUniformSpace.toTopologicalSpace
  letI := quadraticL2InnerProductSpace μ hK hKi
  letI := quadraticSubmodule_finiteDimensional (E := E)
  letI : AddCommGroup (quadraticJetSpace E) :=
    (inferInstance : NormedAddCommGroup (quadraticJetSpace E)).toAddCommGroup
  letI : Module ℝ (quadraticJetSpace E) :=
    (inferInstance : NormedSpace ℝ (quadraticJetSpace E)).toModule
  exact (quadraticJetMap (E := E)).continuous_of_finiteDimensional

theorem quadraticL2JetAt_continuous [FiniteDimensional ℝ E] (x : E) :
    letI := quadraticL2NormedAddCommGroup μ hK hKi
    letI : TopologicalSpace (quadraticSubmodule E) :=
      (quadraticL2NormedAddCommGroup μ hK hKi).toMetricSpace.toUniformSpace.toTopologicalSpace
    Continuous (quadraticJetMapAt (E := E) x) := by
  letI := quadraticL2NormedAddCommGroup μ hK hKi
  letI : TopologicalSpace (quadraticSubmodule E) :=
    (quadraticL2NormedAddCommGroup μ hK hKi).toMetricSpace.toUniformSpace.toTopologicalSpace
  letI := quadraticL2InnerProductSpace μ hK hKi
  letI := quadraticSubmodule_finiteDimensional (E := E)
  letI : AddCommGroup (quadraticJetSpace E) :=
    (inferInstance : NormedAddCommGroup (quadraticJetSpace E)).toAddCommGroup
  letI : Module ℝ (quadraticJetSpace E) :=
    (inferInstance : NormedSpace ℝ (quadraticJetSpace E)).toModule
  exact (quadraticJetMapAt x).continuous_of_finiteDimensional

theorem quadraticL2Evaluation_continuous [FiniteDimensional ℝ E] (x : E) :
    letI := quadraticL2NormedAddCommGroup μ hK hKi
    letI : TopologicalSpace (quadraticSubmodule E) :=
      (quadraticL2NormedAddCommGroup μ hK hKi).toMetricSpace.toUniformSpace.toTopologicalSpace
    Continuous (fun q : quadraticSubmodule E => q.val x) := by
  letI := quadraticL2NormedAddCommGroup μ hK hKi
  letI : TopologicalSpace (quadraticSubmodule E) :=
    (quadraticL2NormedAddCommGroup μ hK hKi).toMetricSpace.toUniformSpace.toTopologicalSpace
  letI := quadraticL2InnerProductSpace μ hK hKi
  letI := quadraticSubmodule_finiteDimensional (E := E)
  let L : quadraticSubmodule E →ₗ[ℝ] ℝ :=
    { toFun := fun q => q.val x, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  exact L.continuous_of_finiteDimensional

theorem pluriharmonicQuadraticL2Ball_isCompact [FiniteDimensional ℝ E]
    {ι : Type*} (a b : ι → E) {ε : ℝ} (hε : 0 ≤ ε) :
    letI := quadraticL2NormedAddCommGroup μ hK hKi
    letI : TopologicalSpace (quadraticSubmodule E) :=
      (quadraticL2NormedAddCommGroup μ hK hKi).toMetricSpace.toUniformSpace.toTopologicalSpace
    IsCompact {q : pluriharmonicQuadraticSubmodule a b |
      quadraticL2Energy μ K q.val.val ≤ ε} := by
  letI := quadraticL2NormedAddCommGroup μ hK hKi
  letI : TopologicalSpace (quadraticSubmodule E) :=
    (quadraticL2NormedAddCommGroup μ hK hKi).toMetricSpace.toUniformSpace.toTopologicalSpace
  letI := quadraticL2InnerProductSpace μ hK hKi
  letI := quadraticSubmodule_finiteDimensional (E := E)
  have he : {q : pluriharmonicQuadraticSubmodule a b | quadraticL2Energy μ K q.val.val ≤ ε} =
      closedBall 0 (Real.sqrt ε) := by
    ext q
    rw [mem_setOf_eq,mem_closedBall,dist_zero_right]
    change quadraticL2Energy μ K q.val.val ≤ ε ↔ ‖q.val‖ ≤ Real.sqrt ε
    rw [← quadraticL2_norm_sq μ hK hKi]
    exact (Real.le_sqrt (norm_nonneg q.val) hε).symm
  rw [he]
  exact isCompact_closedBall _ _

end Geometry
end PowerConvexity
