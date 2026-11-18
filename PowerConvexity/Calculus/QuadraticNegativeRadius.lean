import PowerConvexity.Calculus.QuadraticSmallRadiusTwo

/-! # Separate compact regions for negativity and boundary spectral positivity -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set MeasureTheory
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]

section Negative
variable [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_quadratic_L2_radius_negative
    (μ : Measure E) [IsFiniteMeasureOnCompacts μ] [Measure.IsOpenPosMeasure μ]
    {K X : Set E} (hK : IsCompact K) (hKi : (interior K).Nonempty) (hX : IsCompact X)
    {u : E → ℝ} (hu : ∀ x ∈ X, ContinuousAt u x) (hneg : ∀ x ∈ X, u x < 0) :
    ∃ ε > 0, ∀ q : E → ℝ, IsQuadraticPolynomial q → quadraticL2Energy μ K q ≤ ε →
      ∀ x ∈ X, u x+q x < 0 := by
  letI := quadraticL2NormedAddCommGroup μ hK hKi
  letI : TopologicalSpace (quadraticSubmodule E) :=
    (quadraticL2NormedAddCommGroup μ hK hKi).toMetricSpace.toUniformSpace.toTopologicalSpace
  letI := quadraticL2InnerProductSpace μ hK hKi
  letI := quadraticSubmodule_finiteDimensional (E := E)
  let F : quadraticSubmodule E →ₗ[ℝ] quadraticSubmodule E := LinearMap.id
  let V : quadraticSubmodule E × E → ℝ := fun z => u z.2+(F z.1).val z.2
  have hVc (x : E) (hx : x ∈ X) : ContinuousAt V (0,x) := by
    have hh : ContinuousAt (fun z : E × quadraticSubmodule E => u z.1+(F z.2).val z.1) (x,0) :=
      ((hu x hx).comp (continuousAt_fst (p := (x,0)))).add
        (quadraticFamily_joint_value_contDiff F 0).continuous.continuousAt
    exact hh.comp (f := Prod.swap) (x := (0,x)) continuous_swap.continuousAt
  have hV0 (x : E) (hx : x ∈ X) : V (0,x) < 0 := by
    change u x+0 < 0
    simpa only [add_zero] using hneg x hx
  obtain ⟨r,hr,hh⟩ := compact_small_parameter_negative hX hVc hV0
  refine ⟨r^2,sq_pos_of_pos hr,?_⟩
  intro q hq hEq x hx
  let p : quadraticSubmodule E := ⟨q,hq⟩
  have he : ‖p‖^2 = quadraticL2Energy μ K q := quadraticL2_norm_sq μ hK hKi p
  have hp : ‖p‖ ≤ r := by nlinarith [norm_nonneg p]
  exact hh p hp x hx

end Negative
section Two
variable [NormedSpace ℂ E] [InnerProductSpace ℝ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℂ E] [FiniteDimensional ℝ E]

theorem exists_quadratic_L2_radius_negative_and_boundary_positive_two
    (μ : Measure E) [IsFiniteMeasureOnCompacts μ] [Measure.IsOpenPosMeasure μ]
    {K X B : Set E} (hK : IsCompact K) (hKi : (interior K).Nonempty)
    (hX : IsCompact X) (hB : IsCompact B) (hBX : B ⊆ X)
    (e : Module.Basis (Fin 2) ℂ E) {u : E → ℝ}
    (hu : ∀ x ∈ X, ContDiffAt ℝ 2 u x) (hneg : ∀ x ∈ X, u x < 0)
    (hpos : ∀ x ∈ B, (complexHessian e (fun j => Complex.I • e j) u x).PosDef)
    (hσ : ∀ x ∈ B, 0 < modifiedSigmaTwo e (fun j => Complex.I • e j) u x) :
    ∃ ε > 0, ∀ q : E → ℝ, IsPluriharmonicQuadratic e (fun j => Complex.I • e j) q →
      quadraticL2Energy μ K q ≤ ε →
      (∀ x ∈ X, u x+q x < 0) ∧
      (∀ x ∈ B, 0 < modifiedSigmaTwo e (fun j => Complex.I • e j) (fun y => u y+q y) x) := by
  obtain ⟨ε,hε,hN⟩ := exists_quadratic_L2_radius_negative μ hK hKi hX
    (fun x hx => (hu x hx).continuousAt) hneg
  obtain ⟨δ,hδ,hS⟩ := exists_quadratic_L2_radius_negative_and_positive_sigma_two μ hK hKi hB e
    (fun x hx => hu x (hBX hx)) (fun x hx => hneg x (hBX hx)) hpos hσ
  refine ⟨min ε δ,lt_min hε hδ,?_⟩
  intro q hq he
  exact ⟨hN q hq.1 (he.trans (min_le_left _ _)),
    fun x hx => (hS q hq (he.trans (min_le_right _ _)) x hx).2⟩

end Two
end PowerConvexity
