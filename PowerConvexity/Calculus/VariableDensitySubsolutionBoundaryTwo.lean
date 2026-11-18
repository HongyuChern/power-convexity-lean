import PowerConvexity.Calculus.VariableDensityBoundaryNormalTwo
import PowerConvexity.Calculus.StrictSubsolutionBoundaryJetBoundsTwo

/-! # A fixed ordered subsolution controls variable-density boundary jets

The boundary derivative comparison consumes the actual value order w<=u.
The only density condition on u is det(Hu).re>=1. Constants are selected from
w before any auxiliary solution and never from that solution's unknown jets.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem ordered_boundary_inward_derivative_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U)
    {w u : E → ℝ}
    (hw : ContDiff ℝ 2 w) (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U)
    (hle : ∀ y ∈ closure U, w y ≤ u y)
    (hb : ∀ x ∈ frontier U, w x = u x)
    {x : E} (hx : x ∈ frontier U) :
    ∀ y ∈ closure U, fderiv ℝ w x (y-x) ≤ J.derivative x (y-x) := by
  have hm : IsMinOn (fun z => u z-w z) (closure U) x := by
    intro y hy
    change u x-w x ≤ u y-w y
    rw [← hb x hx,sub_self]
    exact sub_nonneg.mpr (hle y hy)
  have hdu := closureJet_hasFDerivWithinAt hU hconv
    (hu.differentiableOn (by norm_num)) J (frontier_subset_closure hx)
  have hdw : HasFDerivWithinAt w (fderiv ℝ w x) (closure U) x :=
    (hw.contDiffAt.differentiableAt (by norm_num)).hasFDerivAt.hasFDerivWithinAt
  intro y hy
  have hh := hm.localize.hasFDerivWithinAt_nonneg (hdu.sub hdw)
    (sub_mem_posTangentConeAt_of_segment_subset
      (hconv.closure.segment_subset (frontier_subset_closure hx) hy))
  simpa only [ContinuousLinearMap.sub_apply,sub_nonneg] using hh

theorem ordered_subsolution_defining_tangent_upper_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (a b : Fin 2 → E) (hab : Orthonormal ℝ (Sum.elim a b))
    {w u : E → ℝ} (hw : ContDiff ℝ 2 w) (hu : ContDiffOn ℝ 2 u U)
    (J : ClosureC2Jet u U)
    (hwb : ∀ x ∈ frontier U, w x = 0) (hub : ∀ x ∈ frontier U, u x = 0)
    (hwu : ∀ x ∈ closure U, w x ≤ u x)
    (hup : ∀ x ∈ U, (complexHessian a b u x).PosDef)
    (hud : ∀ x ∈ U, (1 : ℝ) ≤ (complexHessian a b u x).det.re)
    {x : E} (hx : x ∈ frontier U) {f : E → ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hfx : f x = 0) (hDf : fderiv ℝ f x ≠ 0)
    (hdef : ∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0) :
    let N := (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x)
    ∃ lam > 0, J.derivative x = lam • fderiv ℝ f x ∧
      lam*‖N‖^2 ≤ fderiv ℝ w x N ∧
      ∀ v : E, fderiv ℝ f x v = 0 →
        J.hessian x v v ≤ (fderiv ℝ w x N/‖N‖^2)*realHessian f x v v := by
  let N := (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x)
  have hNf (v : E) : inner ℝ N v = fderiv ℝ f x v := InnerProductSpace.toDual_symm_apply
  have hN : N ≠ 0 := by
    intro hz
    apply hDf
    ext v
    rw [← hNf,hz,inner_zero_left,ContinuousLinearMap.zero_apply]
  have hNN : fderiv ℝ f x N = ‖N‖^2 := by rw [← hNf,real_inner_self_eq_norm_sq]
  obtain ⟨lam,hlam,hJ,hH⟩ := classicalDirichlet_defining_tangent_hessian_of_det_lower_two
    hU hconv hK hu J hub a b hab hup hud hx hf hfx hDf hdef
  obtain ⟨r,hr,hball⟩ := exists_interior_ball_of_C2_defining_function hf hfx hN
    (fun v => (hNf v).symm) hdef
  have hR : 0 < r*‖N‖ := mul_pos hr (norm_pos_iff.mpr hN)
  have hyU : x-r • N ∈ U := hball (mem_ball_self hR)
  have hcomp := ordered_boundary_inward_derivative_two hU hconv hw hu J hwu (fun y hy => (hwb y hy).trans (hub y hy).symm) hx
    (x-r • N) (subset_closure hyU)
  rw [show x-r • N-x = -r • N by module,hJ] at hcomp
  simp only [map_smul,smul_apply,smul_eq_mul] at hcomp
  rw [hNN] at hcomp
  have hupper : lam*‖N‖^2 ≤ fderiv ℝ w x N := by nlinarith
  have hratio : lam ≤ fderiv ℝ w x N/‖N‖^2 :=
    (le_div_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hN))).mpr hupper
  refine ⟨lam,hlam,hJ,hupper,?_⟩
  intro v hv
  rw [hH v v hv hv]
  exact mul_le_mul_of_nonneg_right hratio
    (definingFunction_tangent_hessian_nonneg_of_convex hU hconv hx hf hfx hDf hdef v hv)

theorem ordered_subsolution_boundary_derivative_norm_le_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (a b : Fin 2 → E) (hab : Orthonormal ℝ (Sum.elim a b))
    {w u : E → ℝ} (hw : ContDiff ℝ 2 w) (hu : ContDiffOn ℝ 2 u U)
    (J : ClosureC2Jet u U)
    (hwb : ∀ x ∈ frontier U, w x = 0) (hub : ∀ x ∈ frontier U, u x = 0)
    (hwu : ∀ x ∈ closure U, w x ≤ u x)
    (hup : ∀ x ∈ U, (complexHessian a b u x).PosDef)
    (hud : ∀ x ∈ U, (1 : ℝ) ≤ (complexHessian a b u x).det.re)
    {x : E} (hx : x ∈ frontier U) {f : E → ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hfx : f x = 0) (hDf : fderiv ℝ f x ≠ 0)
    (hdef : ∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0) :
    ‖J.derivative x‖ ≤ ‖fderiv ℝ w x‖ := by
  let N := (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x)
  have hnorm : ‖N‖ = ‖fderiv ℝ f x‖ :=
    (InnerProductSpace.toDual ℝ E).symm.norm_map _
  have hN : 0 < ‖N‖ := by rw [hnorm]; exact norm_pos_iff.mpr hDf
  obtain ⟨lam,hlam,hJ,hbound,_⟩ := ordered_subsolution_defining_tangent_upper_two
    hU hconv hK a b hab hw hu J hwb hub hwu hup hud hx hf hfx hDf hdef
  have hop : fderiv ℝ w x N ≤ ‖fderiv ℝ w x‖*‖N‖ :=
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using (fderiv ℝ w x).le_opNorm N)
  have hmul : (lam*‖N‖)*‖N‖ ≤ ‖fderiv ℝ w x‖*‖N‖ := by
    change lam*‖N‖^2 ≤ fderiv ℝ w x N at hbound
    nlinarith
  rw [hJ,norm_smul,Real.norm_eq_abs,abs_of_pos hlam,← hnorm]
  exact (mul_le_mul_iff_left₀ hN).mp hmul

theorem ordered_subsolution_boundary_tangent_hessian_le_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (a b : Fin 2 → E) (hab : Orthonormal ℝ (Sum.elim a b))
    {w u : E → ℝ} (hw : ContDiff ℝ 2 w) (hu : ContDiffOn ℝ 2 u U)
    (J : ClosureC2Jet u U)
    (hwb : ∀ x ∈ frontier U, w x = 0) (hub : ∀ x ∈ frontier U, u x = 0)
    (hwu : ∀ x ∈ closure U, w x ≤ u x)
    (hup : ∀ x ∈ U, (complexHessian a b u x).PosDef)
    (hud : ∀ x ∈ U, (1 : ℝ) ≤ (complexHessian a b u x).det.re)
    {x : E} (hx : x ∈ frontier U) {f : E → ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hfx : f x = 0) (hDf : fderiv ℝ f x ≠ 0)
    (hdef : ∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0)
    (v : E) (hv : fderiv ℝ f x v = 0) :
    J.hessian x v v ≤ realHessian w x v v := by
  obtain ⟨lam,hlam,hJ,hbound,hupper⟩ := ordered_subsolution_defining_tangent_upper_two
    hU hconv hK a b hab hw hu J hwb hub hwu hup hud hx hf hfx hDf hdef
  have he := (zero_boundary_function_defining_derivative_hessian
    hU hf hfx hDf hdef hw.contDiffAt hwb).2 v v hv hv
  rw [he]
  exact hupper v hv

theorem ordered_subsolution_uniform_boundary_first_tangent_bounds_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hboundary : HasC2LocalDefiningFunction U)
    (a b : Fin 2 → E) (hab : Orthonormal ℝ (Sum.elim a b))
    {w : E → ℝ} (hw : ContDiff ℝ 4 w)
    (hwb : ∀ x ∈ frontier U, w x = 0)
    :
    ∃ C ≥ 0, ∀ (u : E → ℝ) (J : ClosureC2Jet u U),
      ContDiffOn ℝ 2 u U →
      (∀ x ∈ frontier U, u x = 0) →
      (∀ x ∈ U, (complexHessian a b u x).PosDef) →
      (∀ x ∈ U, (1 : ℝ) ≤ (complexHessian a b u x).det.re) →
      (∀ x ∈ closure U, w x ≤ u x) →
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
  intro u J hu hub hup hud hwu x hx
  obtain ⟨f,hf,hfx,hDf,hdef⟩ := hboundary x hx
  refine ⟨(ordered_subsolution_boundary_derivative_norm_le_two
    hU hconv hK a b hab hw2 hu J hwb hub hwu hup hud hx hf hfx hDf hdef).trans
      ((hA x (frontier_subset_closure hx)).trans hAC),?_⟩
  intro v hv
  obtain ⟨lam,hlam,hJ⟩ := classicalDirichlet_derivative_eq_positive_defining_multiple_of_det_lower_two
    hU hconv hK hu J hub a b hab hup hud hx hf hfx hDf hdef
  have hfv : fderiv ℝ f x v = 0 := by
    rw [hJ] at hv
    simp only [ContinuousLinearMap.smul_apply,smul_eq_mul] at hv
    exact (mul_eq_zero.mp hv).resolve_left hlam.ne'
  have hupper := ordered_subsolution_boundary_tangent_hessian_le_two
    hU hconv hK a b hab hw2 hu J hwb hub hwu hup hud hx hf hfx hDf hdef v hfv
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
