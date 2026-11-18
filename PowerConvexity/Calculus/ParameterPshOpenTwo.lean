import PowerConvexity.Calculus.ParameterStrictSubsolutionScalingTwo
import PowerConvexity.Calculus.PairedBilinearContinuity
import PowerConvexity.Calculus.ComplexLeviPairPositiveTwo

/-! # Openness of actual strict psh for a jointly C2 family -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Filter
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
noncomputable section
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E]
local instance ppoRealSpace : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance ppoRealModule : Module ℝ E := (inferInstance : InnerProductSpace ℝ E).toModule
local instance ppoDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance ppoDualModule : Module ℝ (E →L[ℝ] ℝ) :=
  (inferInstance : NormedSpace ℝ (E →L[ℝ] ℝ)).toModule
local instance ppoDualTopology : TopologicalSpace (E →L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance ppoHessAddGroup : AddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ)).toAddCommGroup
local instance ppoHessSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance ppoHessModule : Module ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  (inferInstance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ)).toModule
local instance ppoHessTopology : TopologicalSpace (E →L[ℝ] E →L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace

theorem parameter_complexHessian_posDef_eventually_of_joint_C2_two
    (e : Module.Basis (Fin 2) ℂ E) {F : ℝ × E → ℝ} {p : ℝ × E}
    (hF : ContDiffAt ℝ 2 F p)
    (hp : (complexHessian e (fun j => Complex.I • e j) (fun y => F (p.1,y)) p.2).PosDef) :
    ∀ᶠ q : ℝ × E in 𝓝 p,
      (complexHessian e (fun j => Complex.I • e j) (fun y => F (q.1,y)) q.2).PosDef := by
  let I : E →L[ℝ] E := (Complex.I • ContinuousLinearMap.id ℂ E).restrictScalars ℝ
  have hI (v : E) : I v = Complex.I • v := rfl
  have hD : ContDiffAt ℝ 1
      (fun q : ℝ × E => fderiv ℝ (fun y => F (q.1,y)) q.2) p :=
    parameter_fiber_fderiv_contDiffAt (n := 1) hF
  have hH : ContinuousAt
      (fun q : ℝ × E => realHessian (fun y => F (q.1,y)) q.2) p :=
    (parameter_fiber_fderiv_contDiffAt (n := 0) hD).continuousAt
  have hQ : ContinuousAt
      (fun q : ℝ × E => pairedBilinearForm I (realHessian (fun y => F (q.1,y)) q.2)) p :=
    (continuous_pairedBilinearForm I).continuousAt.comp hH
  have hfiber : ContDiffAt ℝ 2 (fun y => F (p.1,y)) p.2 :=
    hF.comp p.2 (contDiffAt_const.prodMk contDiffAt_id)
  have hpair : ∀ v : E, v ≠ 0 →
      0 < pairedBilinearForm I (realHessian (fun y => F (p.1,y)) p.2) v v := by
    simpa only [pairedBilinearForm_apply,hI] using
      complexHessian_posDef_paired_positive_two e hfiber hp
  filter_upwards [hF.eventually (by norm_num),
    hQ.tendsto.eventually (isOpen_positive_bilinear_forms.mem_nhds hpair)] with q hq hpos
  have hqfiber : ContDiffAt ℝ 2 (fun y => F (q.1,y)) q.2 :=
    hq.comp q.2 (contDiffAt_const.prodMk contDiffAt_id)
  apply complexHessian_posDef_of_paired_positive_two e hqfiber
  simpa only [pairedBilinearForm_apply,hI] using hpos

end
end PowerConvexity
