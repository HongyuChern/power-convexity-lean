import PowerConvexity.Calculus.SubsolutionTangentialBoundaryUpperTwo
import PowerConvexity.Calculus.BoundaryZeroTangentHessian
import Mathlib.Analysis.Normed.Group.Bounded

/-! # Boundary first and tangent second jets controlled by a fixed strict subsolution

The comparison barrier is independent of the unknown solution. The actual
tangent Hessian is bounded above by the actual Hessian of that same barrier.
Mixed normal/tangent second derivatives are not estimated here.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Filter
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem strict_subsolution_boundary_derivative_norm_le_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (a b : Fin 2 → E) (hab : Orthonormal ℝ (Sum.elim a b))
    {w u : E → ℝ} (hw : ContDiff ℝ 2 w) (hu : ContDiffOn ℝ 2 u U)
    (J : ClosureC2Jet u U)
    (hwb : ∀ x ∈ frontier U, w x = 0) (hub : ∀ x ∈ frontier U, u x = 0)
    (hwp : ∀ x ∈ U, (complexHessian a b w x).PosDef)
    (hwd : ∀ x ∈ U, (1 : ℂ) < (complexHessian a b w x).det)
    (hup : ∀ x ∈ U, (complexHessian a b u x).PosDef)
    (hud : ∀ x ∈ U, (complexHessian a b u x).det = 1)
    {x : E} (hx : x ∈ frontier U) {f : E → ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hfx : f x = 0) (hDf : fderiv ℝ f x ≠ 0)
    (hdef : ∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0) :
    ‖J.derivative x‖ ≤ ‖fderiv ℝ w x‖ := by
  let N := (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x)
  have hnorm : ‖N‖ = ‖fderiv ℝ f x‖ :=
    (InnerProductSpace.toDual ℝ E).symm.norm_map _
  have hN : 0 < ‖N‖ := by rw [hnorm]; exact norm_pos_iff.mpr hDf
  obtain ⟨lam,hlam,hJ,hbound,_⟩ := strict_subsolution_defining_tangent_upper_two
    hU hconv hK a b hab hw hu J hwb hub hwp hwd hup hud hx hf hfx hDf hdef
  have hop : fderiv ℝ w x N ≤ ‖fderiv ℝ w x‖*‖N‖ :=
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using (fderiv ℝ w x).le_opNorm N)
  have hmul : (lam*‖N‖)*‖N‖ ≤ ‖fderiv ℝ w x‖*‖N‖ := by
    change lam*‖N‖^2 ≤ fderiv ℝ w x N at hbound
    nlinarith
  rw [hJ,norm_smul,Real.norm_eq_abs,abs_of_pos hlam,← hnorm]
  exact (mul_le_mul_iff_left₀ hN).mp hmul

theorem strict_subsolution_boundary_tangent_hessian_le_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (a b : Fin 2 → E) (hab : Orthonormal ℝ (Sum.elim a b))
    {w u : E → ℝ} (hw : ContDiff ℝ 2 w) (hu : ContDiffOn ℝ 2 u U)
    (J : ClosureC2Jet u U)
    (hwb : ∀ x ∈ frontier U, w x = 0) (hub : ∀ x ∈ frontier U, u x = 0)
    (hwp : ∀ x ∈ U, (complexHessian a b w x).PosDef)
    (hwd : ∀ x ∈ U, (1 : ℂ) < (complexHessian a b w x).det)
    (hup : ∀ x ∈ U, (complexHessian a b u x).PosDef)
    (hud : ∀ x ∈ U, (complexHessian a b u x).det = 1)
    {x : E} (hx : x ∈ frontier U) {f : E → ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hfx : f x = 0) (hDf : fderiv ℝ f x ≠ 0)
    (hdef : ∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0)
    (v : E) (hv : fderiv ℝ f x v = 0) :
    J.hessian x v v ≤ realHessian w x v v := by
  obtain ⟨lam,hlam,hJ,hbound,hupper⟩ := strict_subsolution_defining_tangent_upper_two
    hU hconv hK a b hab hw hu J hwb hub hwp hwd hup hud hx hf hfx hDf hdef
  have he := (zero_boundary_function_defining_derivative_hessian
    hU hf hfx hDf hdef hw.contDiffAt hwb).2 v v hv hv
  rw [he]
  exact hupper v hv

theorem strict_subsolution_uniform_boundary_first_tangent_bounds_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hboundary : HasC2LocalDefiningFunction U)
    (a b : Fin 2 → E) (hab : Orthonormal ℝ (Sum.elim a b))
    {w : E → ℝ} (hw : ContDiff ℝ 4 w)
    (hwb : ∀ x ∈ frontier U, w x = 0)
    (hwp : ∀ x ∈ U, (complexHessian a b w x).PosDef)
    (hwd : ∀ x ∈ U, (1 : ℂ) < (complexHessian a b w x).det) :
    ∃ C ≥ 0, ∀ (u : E → ℝ) (J : ClosureC2Jet u U),
      ContDiffOn ℝ 2 u U →
      (∀ x ∈ frontier U, u x = 0) →
      (∀ x ∈ U, (complexHessian a b u x).PosDef) →
      (∀ x ∈ U, (complexHessian a b u x).det = 1) →
      ∀ x ∈ frontier U, ‖J.derivative x‖ ≤ C ∧
        ∀ v : E, J.derivative x v = 0 → J.hessian x v v ≤ C*‖v‖^2 := by
  letI : AddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
    (inferInstance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ)).toAddCommGroup
  letI : Module ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
    (inferInstance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ)).toModule
  letI : TopologicalSpace (E →L[ℝ] E →L[ℝ] ℝ) :=
    (inferInstance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace
  have hw2 : ContDiff ℝ 2 w := hw.of_le (by norm_num)
  have hDc : Continuous (fderiv ℝ w) := (hw.fderiv_right (m := 3) (by norm_num)).continuous
  have hHc : Continuous (realHessian w) :=
    ((hw.fderiv_right (m := 3) (by norm_num)).fderiv_right (m := 2) (by norm_num)).continuous
  obtain ⟨A,hA⟩ := hK.exists_bound_of_continuousOn hDc.continuousOn
  have hEval : Continuous (fun p : E × E => realHessian w p.1 p.2 p.2) :=
    ((hHc.comp continuous_fst).clm_apply continuous_snd).clm_apply continuous_snd
  obtain ⟨B,hB⟩ := (hK.prod (isCompact_sphere (0 : E) 1)).exists_bound_of_continuousOn
    hEval.continuousOn
  let C := max 0 (max A B)
  have hAC : A ≤ C := (le_max_left A B).trans (le_max_right 0 (max A B))
  have hBC : B ≤ C := (le_max_right A B).trans (le_max_right 0 (max A B))
  refine ⟨C,le_max_left _ _,?_⟩
  intro u J hu hub hup hud x hx
  obtain ⟨f,hf,hfx,hDf,hdef⟩ := hboundary x hx
  refine ⟨(strict_subsolution_boundary_derivative_norm_le_two
    hU hconv hK a b hab hw2 hu J hwb hub hwp hwd hup hud hx hf hfx hDf hdef).trans
      ((hA x (frontier_subset_closure hx)).trans hAC),?_⟩
  intro v hv
  obtain ⟨lam,hlam,hJ⟩ := classicalDirichlet_derivative_eq_positive_defining_multiple_two
    hU hconv hK hu J hub a b hab hup hud hx hf hfx hDf hdef
  have hfv : fderiv ℝ f x v = 0 := by
    rw [hJ] at hv
    simp only [ContinuousLinearMap.smul_apply,smul_eq_mul] at hv
    exact (mul_eq_zero.mp hv).resolve_left hlam.ne'
  have hupper := strict_subsolution_boundary_tangent_hessian_le_two
    hU hconv hK a b hab hw2 hu J hwb hub hwp hwd hup hud hx hf hfx hDf hdef v hfv
  apply hupper.trans
  by_cases hv0 : v = 0
  · simp [hv0]
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  let z := ‖v‖⁻¹ • v
  have hz : ‖z‖ = 1 := by simp [z,norm_smul,hvn.ne']
  have hvz : ‖v‖ • z = v := by simp [z,smul_smul,hvn.ne']
  have hzB : realHessian w x z z ≤ B := (le_abs_self _).trans (by
    simpa only [Real.norm_eq_abs] using hB (x,z)
      ⟨frontier_subset_closure hx,by simpa only [Metric.mem_sphere,dist_zero_right] using hz⟩)
  have he : realHessian w x v v = ‖v‖^2*realHessian w x z z := by
    conv_lhs => rw [← hvz]
    simp only [map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul]
    ring
  rw [he,mul_comm C]
  exact mul_le_mul_of_nonneg_left (hzB.trans hBC) (sq_nonneg _)

end PowerConvexity
