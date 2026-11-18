import PowerConvexity.Calculus.PoissonKernelFour
import PowerConvexity.Analysis.CompactParameterIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Actual C2 harmonic Poisson integrals in four real dimensions.
The boundary function is only continuous on the actual unit sphere.
All parameter derivative fields are the actual derivatives of the kernel.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
local notation "E" => DeGiorgi.AmbientSpace (2+2)
local notation "S" => sphere (0 : E) 1
local notation "J" => Fin 2 ⊕ Fin 2
local instance cat3 : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance cat4 : Module ℝ (E →L[ℝ] ℝ) :=
  (inferInstance : NormedSpace ℝ (E →L[ℝ] ℝ)).toModule
local instance cat5 : TopologicalSpace (E →L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance cat6 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance cat7 : Module ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  (inferInstance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ)).toModule
local instance cat8 : TopologicalSpace (E →L[ℝ] E →L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance testCE : ContinuousENorm (E →L[ℝ] E →L[ℝ] ℝ) :=
  @SeminormedAddGroup.toContinuousENorm (E →L[ℝ] E →L[ℝ] ℝ) inferInstance

theorem poissonKernelFour_fderiv_joint_contDiffAt {z : E × E}
    (hne : z.1 ≠ z.2) (n : ℕ∞ω) :
    ContDiffAt ℝ n (fun p : E × E => fderiv ℝ (poissonKernelFour p.2) p.1) z := by
  have h := (poissonKernelFour_joint_contDiffAt hne (n+1)).comp (z,z.1)
    (contDiffAt_snd.prodMk contDiffAt_fst.snd)
  exact h.fderiv contDiffAt_fst le_rfl

theorem poissonKernelFour_hessian_joint_contDiffAt {z : E × E}
    (hne : z.1 ≠ z.2) (n : ℕ∞ω) :
    ContDiffAt ℝ n (fun p : E × E => realHessian (poissonKernelFour p.2) p.1) z := by
  have h := (poissonKernelFour_fderiv_joint_contDiffAt hne (n+1)).comp (z,z.1)
    (contDiffAt_snd.prodMk contDiffAt_fst.snd)
  exact h.fderiv contDiffAt_fst le_rfl

theorem unitBall_point_ne_unitSphere_four {x : E} (hx : x ∈ ball 0 1) (ξ : S) :
    x ≠ (ξ : E) := by
  intro he
  have hnorm : ‖(ξ : E)‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using ξ.property
  simpa [he,mem_ball,dist_zero_right,hnorm] using hx

private theorem restrict_offDiagonal_continuousOn {G : Type*} [TopologicalSpace G]
    {F : E × E → G} (hF : ∀ z : E × E, z.1 ≠ z.2 → ContinuousAt F z) :
    ContinuousOn (fun p : E × S => F (p.1,p.2)) (ball 0 1 ×ˢ univ) := by
  intro p hp
  have hm : ContinuousAt (fun q : E × S => (q.1,(q.2 : E))) p :=
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).continuousAt
  have hh : ContinuousAt (fun q : E × S => F (q.1,(q.2 : E))) p :=
    (hF (p.1,p.2) (unitBall_point_ne_unitSphere_four hp.1 p.2)).comp
      (f := fun q : E × S => (q.1,(q.2 : E))) hm
  exact hh.continuousWithinAt

def poissonIntegralFour (μ : Measure S) (f : S → ℝ) (x : E) : ℝ :=
  ∫ ξ, f ξ*poissonKernelFour ξ x ∂μ

private theorem poisson_integrand_fields {f : S → ℝ} (hf : Continuous f) :
    ContinuousOn (fun p : E × S => f p.2*poissonKernelFour p.2 p.1) (ball 0 1 ×ˢ univ) ∧
    ContinuousOn (fun p : E × S => f p.2 • fderiv ℝ (poissonKernelFour p.2) p.1) (ball 0 1 ×ˢ univ) ∧
    ContinuousOn (fun p : E × S => f p.2 • realHessian (poissonKernelFour p.2) p.1) (ball 0 1 ×ˢ univ) ∧
    (∀ x ∈ ball (0 : E) 1, ∀ ξ : S,
      HasFDerivAt (fun y => f ξ*poissonKernelFour ξ y)
        (f ξ • fderiv ℝ (poissonKernelFour ξ) x) x) ∧
    (∀ x ∈ ball (0 : E) 1, ∀ ξ : S,
      HasFDerivAt (fun y => f ξ • fderiv ℝ (poissonKernelFour ξ) y)
        (f ξ • realHessian (poissonKernelFour ξ) x) x) := by
  have h0 := restrict_offDiagonal_continuousOn
    (fun z hz => (poissonKernelFour_joint_contDiffAt hz 0).continuousAt)
  have h1 := restrict_offDiagonal_continuousOn
    (fun z hz => (poissonKernelFour_fderiv_joint_contDiffAt hz 0).continuousAt)
  have h2 := restrict_offDiagonal_continuousOn
    (fun z hz => (poissonKernelFour_hessian_joint_contDiffAt hz 0).continuousAt)
  refine ⟨(hf.comp continuous_snd).continuousOn.mul h0,
    (hf.comp continuous_snd).continuousOn.smul h1,
    (hf.comp continuous_snd).continuousOn.smul h2,?_,?_⟩
  · intro x hx ξ
    exact ((poissonKernelFour_contDiffAt (unitBall_point_ne_unitSphere_four hx ξ) 1).differentiableAt
      (by norm_num)).hasFDerivAt.const_mul (f ξ)
  · intro x hx ξ
    exact (((poissonKernelFour_contDiffAt (unitBall_point_ne_unitSphere_four hx ξ) 2).fderiv_right
      (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt.const_smul (f ξ)

theorem poissonIntegralFour_C2_and_hessian (μ : Measure S) [IsFiniteMeasure μ]
    {f : S → ℝ} (hf : Continuous f) :
    ContDiffOn ℝ 2 (poissonIntegralFour μ f) (ball 0 1) ∧
    ∀ x ∈ ball (0 : E) 1, realHessian (poissonIntegralFour μ f) x =
      ∫ ξ, f ξ • realHessian (poissonKernelFour ξ) x ∂μ := by
  obtain ⟨h0,h1,h2,hd,hdd⟩ := poisson_integrand_fields hf
  refine ⟨compact_parameter_integral_C2 isOpen_ball h0 h1 h2 hd hdd,?_⟩
  intro x hx
  have heq : fderiv ℝ (poissonIntegralFour μ f) =ᶠ[𝓝 x]
      fun y => ∫ ξ, f ξ • fderiv ℝ (poissonKernelFour ξ) y ∂μ := by
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    exact (compact_parameter_integral_hasFDerivAt isOpen_ball h0 h1 hd hy).fderiv
  unfold realHessian
  rw [heq.fderiv_eq]
  exact (compact_parameter_integral_hasFDerivAt isOpen_ball h1 h2 hdd hx).fderiv

def realBlockTraceFormFour : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] ℝ :=
  ∑ i : J, (ContinuousLinearMap.apply ℝ ℝ (Sum.elim realDirections imagDirections i)).comp
    (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) (Sum.elim realDirections imagDirections i))

theorem realBlockTraceFormFour_apply (H : E →L[ℝ] E →L[ℝ] ℝ) :
    realBlockTraceFormFour H =
      ∑ i : J, H (Sum.elim realDirections imagDirections i) (Sum.elim realDirections imagDirections i) := by
  simp [realBlockTraceFormFour]

theorem poissonIntegralFour_harmonic_on_unit_ball (μ : Measure S) [IsFiniteMeasure μ]
    {f : S → ℝ} (hf : Continuous f) :
    InnerProductSpace.HarmonicOnNhd (poissonIntegralFour μ f) (ball 0 1) := by
  obtain ⟨hC2,hH⟩ := poissonIntegralFour_C2_and_hessian μ hf
  have ht (x : E) (hx : x ∈ ball (0 : E) 1) :
      (realBlockHessian realDirections imagDirections (poissonIntegralFour μ f) x).trace = 0 := by
    change realBlockTraceFormFour (realHessian (poissonIntegralFour μ f) x) = 0
    rw [hH x hx]
    have h2 := (poisson_integrand_fields hf).2.2.1
    have hc : Continuous (fun ξ : S => f ξ • realHessian (poissonKernelFour ξ) x) :=
      continuousOn_univ.mp (h2.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun ξ _ => ⟨hx,mem_univ ξ⟩))
    have hi : Integrable (fun ξ : S => f ξ • realHessian (poissonKernelFour ξ) x) μ :=
      hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hcomm := realBlockTraceFormFour.integral_comp_comm hi
    rw [← hcomm]
    have hz (ξ : S) : realBlockTraceFormFour (f ξ • realHessian (poissonKernelFour ξ) x) = 0 := by
      rw [map_smul,realBlockTraceFormFour_apply]
      have hnorm : ‖(ξ : E)‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using ξ.property
      have hh := (poissonKernelFour_harmonic_on_unit_ball hnorm x hx).2.self_of_nhds
      rw [← actual_block_trace_eq_laplacian_two] at hh
      change f ξ • (realBlockHessian realDirections imagDirections (poissonKernelFour ξ) x).trace = 0
      rw [hh]
      simp
    simp_rw [hz]
    exact integral_zero _ _
  intro x hx
  refine ⟨hC2.contDiffAt (isOpen_ball.mem_nhds hx),?_⟩
  filter_upwards [isOpen_ball.mem_nhds hx] with y hy
  change Laplacian.laplacian (poissonIntegralFour μ f) y = 0
  rw [← actual_block_trace_eq_laplacian_two,ht y hy]

end PowerConvexity
