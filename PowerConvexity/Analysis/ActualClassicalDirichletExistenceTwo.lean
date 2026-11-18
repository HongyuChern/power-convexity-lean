import PowerConvexity.Analysis.ActualIsometricHolderDeterminantInverseTwo
import PowerConvexity.Analysis.ActualContinuationOpennessFromInverseTwo
import PowerConvexity.Analysis.ActualContinuationClopenEndpointTwo

/-! # Actual classical Dirichlet existence by the original continuity method

All analytic continuation inputs are proved for the same solutions. The
subsolution and defining function are actual functions on the original
domain. No unknown solution, boundary modulus, or linear inverse is an input.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 1024
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E]
local instance acdeRealSpace : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance acdeRealModule : Module ℝ E := (inferInstance : InnerProductSpace ℝ E).toModule
attribute [local instance] atjInstance1 atjInstance2 atjInstance3 atjInstance4 atjInstance5 atjInstance6
  actualDensityJetSeminormed

theorem actual_continuation_classical_solvable_isOpen_two
    {U : Set E} (hU : IsOpen U) (hne : U.Nonempty)
    (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hgeometry : HasC2LocalDefiningFunction U)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {w : E → ℝ} (hw : ContDiff ℝ 6 w) (hwb : ∀ y ∈ frontier U, w y=0)
    (hwp : ∀ y ∈ closure U, (complexHessian e (fun j => Complex.I • e j) w y).PosDef)
    (hwd : ∀ y ∈ closure U, (1 : ℝ) ≤ (complexHessian e (fun j => Complex.I • e j) w y).det.re)
    {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hfb : ∀ x ∈ frontier U, f x=0 ∧ fderiv ℝ f x≠0)
    (hdef : ∀ x ∈ frontier U, ∀ᶠ z in 𝓝 x, z∈U ↔ f z<0) :
    IsOpen {s : Icc (0 : ℝ) 1 | ∃ u : E → ℝ,
      ClassicalDirichletDensityDataTwo e (fun j => Complex.I • e j) U
        (dirichletContinuationDensityTwo e (fun j => Complex.I • e j) w s) u} := by
  letI : CompactSpace (closure U) := isCompact_iff_compactSpace.mp hK
  obtain ⟨T,hTa,hTb⟩ := exists_euclideanIsometry_complexFrame_two e hab
  have hproper : U≠univ := by
    intro h
    have hcompact : IsCompact (T ⁻¹' closure U) := T.toHomeomorph.isCompact_preimage.mpr hK
    apply hcompact.ne_univ
    simp only [h,closure_univ,preimage_univ]
  obtain ⟨o,ho⟩ := hne
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds ho)
  have hr0 : 0<r/2 := half_pos hr
  have hball0 : closedBall o (r/2)⊆U :=
    (closedBall_subset_ball (half_lt_self hr)).trans hball
  obtain ⟨D,hD⟩ := hK.exists_bound_of_continuousOn
    (f := fun x : E => o-x) (continuous_const.sub continuous_id).continuousOn
  have hdia : 0≤max 0 D := le_max_left _ _
  have hdiam : ∀ c∈frontier U, ‖o-c‖≤max 0 D := fun c hc =>
    (hD c (frontier_subset_closure hc)).trans (le_max_right _ _)
  apply actual_continuation_classical_solvable_isOpen_of_bounded_inverse_two
    hU hconv hK hgeometry e hab hw hwb hwp hwd hf hfb hdef
  intro alpha ha ha1 s p hu
  exact actual_isometric_holder_jet_determinant_bounded_inverse_two hU hK hproper hconv
    hr0 hdia hball0 hdiam hf (fun c hc => (hfb c hc).1) (fun c hc => (hfb c hc).2)
    hdef ha ha1 T e (fun j => Complex.I • e j) hTa hTb (hw.of_le (by norm_num)) hwp hwb
    p hu.1 hu.2.2.1 hu.2.2.2.1
    ((dirichletContinuationDensityTwo_contDiff_C4 e (fun j => Complex.I • e j) hw s).of_le (by norm_num))
    (fun x hx => (dirichletContinuationDensityTwo_bounds e (fun j => Complex.I • e j)
      s.property (hwd x (subset_closure hx))).1)

theorem actual_classical_dirichlet_exists_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hgeometry : HasC2LocalDefiningFunction U)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {w : E → ℝ} (hw : ContDiff ℝ 6 w) (hwb : ∀ y ∈ frontier U, w y=0)
    (hwp : ∀ y ∈ closure U, (complexHessian e (fun j => Complex.I • e j) w y).PosDef)
    (hwd : ∀ y ∈ closure U, (1 : ℝ) ≤ (complexHessian e (fun j => Complex.I • e j) w y).det.re)
    {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hfb : ∀ x ∈ frontier U, f x=0 ∧ fderiv ℝ f x≠0)
    (hdef : ∀ x ∈ frontier U, ∀ᶠ z in 𝓝 x, z∈U ↔ f z<0) :
    ∃ u : E → ℝ, ClassicalDirichletDataTwo e (fun j => Complex.I • e j) U u := by
  by_cases hne : U.Nonempty
  · exact actual_continuation_classical_endpoint_of_open_two hU hconv hK hgeometry e hab
      hw hwb hwp hwd hf hfb hdef
      (actual_continuation_classical_solvable_isOpen_two hU hne hconv hK hgeometry e hab
        hw hwb hwp hwd hf hfb hdef)
  · have he : U=∅ := Set.not_nonempty_iff_eq_empty.mp hne
    refine ⟨w,(hw.of_le (by norm_num)).contDiffOn,?_,?_,?_,hwb⟩
    · exact (c2OnClosure_of_neighborhood (U := U) isOpen_univ (subset_univ _)
        (hw.of_le (by norm_num : (2 : ℕ∞ω)≤6)).contDiffOn).2
    · intro x hx
      exact hwp x (subset_closure hx)
    · intro x hx
      simp only [he,mem_empty_iff_false] at hx

end PowerConvexity
