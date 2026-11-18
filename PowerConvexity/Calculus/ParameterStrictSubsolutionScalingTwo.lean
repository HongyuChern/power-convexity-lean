import PowerConvexity.Calculus.ParameterFiberDerivative
import PowerConvexity.Calculus.LocalDirichletSubsolutionTwo

/-! # One strict-subsolution scaling on a joint parameter-space neighborhood -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
noncomputable section
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
local instance pcsDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance pcsDualModule : Module ℝ (E →L[ℝ] ℝ) :=
  (inferInstance : NormedSpace ℝ (E →L[ℝ] ℝ)).toModule
local instance pcsDualTopology : TopologicalSpace (E →L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance pcsHessAddGroup : AddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ)).toAddCommGroup
local instance pcsHessSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance pcsHessModule : Module ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  (inferInstance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ)).toModule
local instance pcsHessTopology : TopologicalSpace (E →L[ℝ] E →L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace

theorem parameter_complexHessian_continuousAt_of_joint_C2
    {ι : Type*} (a b : ι → E) {F : ℝ × E → ℝ} {p : ℝ × E}
    (hF : ContDiffAt ℝ 2 F p) :
    ContinuousAt (fun q : ℝ × E => complexHessian a b (fun y => F (q.1,y)) q.2) p := by
  have hD : ContDiffAt ℝ 1
      (fun q : ℝ × E => fderiv ℝ (fun y => F (q.1,y)) q.2) p :=
    parameter_fiber_fderiv_contDiffAt (n := 1) hF
  have hH : ContinuousAt (fun q : ℝ × E => realHessian (fun y => F (q.1,y)) q.2) p :=
    (parameter_fiber_fderiv_contDiffAt (n := 0) hD).continuousAt
  apply ((continuous_jetComplexHessian a b).continuousAt.comp hH).congr
  filter_upwards [hF.eventually (by norm_num)] with q hq
  funext i j
  exact (complexHessian_real_entry
    (hq.comp q.2 (contDiffAt_const.prodMk contDiffAt_id)) a b i j).symm

theorem exists_parameter_positive_scaling_det_gt_one_two
    (a b : Fin 2 → E) {F : ℝ × E → ℝ} {p : ℝ × E}
    (hf : ContDiffAt ℝ 2 F p)
    (hp : ∀ᶠ q : ℝ × E in 𝓝 p,
      (complexHessian a b (fun y => F (q.1,y)) q.2).PosDef) :
    ∃ c > 0, ∀ᶠ q : ℝ × E in 𝓝 p,
      (complexHessian a b (fun y => c*F (q.1,y)) q.2).PosDef ∧
      (1 : ℂ) < (complexHessian a b (fun y => c*F (q.1,y)) q.2).det := by
  have hp0 := hp.self_of_nhds
  let d := (complexHessian a b (fun y => F (p.1,y)) p.2).det.re/2
  have hd : 0 < d := half_pos (Complex.pos_iff.mp hp0.det_pos).1
  let c := 1/d+1
  have hc : 0 < c := by dsimp only [c]; positivity
  have hc1 : 1 < c := by dsimp only [c]; linarith [div_pos (by norm_num : (0 : ℝ) < 1) hd]
  have hcd : c*d = 1+d := by dsimp only [c]; rw [add_mul,one_mul,div_mul_cancel₀ _ hd.ne']
  have hcd1 : 1 < c*d := by rw [hcd]; linarith
  have hc2d : 1 < c^2*d := by
    have hh := mul_le_mul_of_nonneg_right hc1.le (mul_nonneg hc.le hd.le)
    nlinarith
  have hdetc : ContinuousAt (fun q : ℝ × E => (complexHessian a b (fun y => F (q.1,y)) q.2).det.re) p :=
    ((Complex.continuous_re.comp continuous_id.matrix_det).continuousAt).comp
      (parameter_complexHessian_continuousAt_of_joint_C2 a b hf)
  have hsmall : d < (complexHessian a b (fun y => F (p.1,y)) p.2).det.re := half_lt_self (Complex.pos_iff.mp hp0.det_pos).1
  refine ⟨c,hc,?_⟩
  filter_upwards [hp,hf.eventually (by simp),hdetc.tendsto.eventually (lt_mem_nhds hsmall)]
    with q hpq hfq hdq
  let f : E → ℝ := fun y => F (q.1,y)
  have hfy : ContDiffAt ℝ 2 f q.2 := hfq.comp q.2 (contDiffAt_const.prodMk contDiffAt_id)
  have hpy : (complexHessian a b f q.2).PosDef := hpq
  have hdy : d < (complexHessian a b f q.2).det.re := hdq
  have hscale := complexHessian_const_mul_at hfy c a b
  have hpos : (complexHessian a b (fun z => c*f z) q.2).PosDef := by
    rw [hscale]
    exact hpy.smul (show (0 : ℂ) < (c : ℂ) from Complex.pos_iff.mpr ⟨hc,by simp⟩)
  refine ⟨hpos,?_⟩
  have hreal : (complexHessian a b (fun z => c*f z) q.2).det.re =
      c^2*(complexHessian a b f q.2).det.re := by
    rw [hscale,Matrix.det_smul]
    simp [Complex.mul_re,Complex.mul_im,pow_two]
  change (1 : ℂ) < (complexHessian a b (fun z => c*f z) q.2).det
  apply Complex.lt_def.mpr
  constructor
  · simp only [Complex.one_re,hreal]
    have hh := mul_le_mul_of_nonneg_left hdy.le (sq_nonneg c)
    linarith
  · simpa only [Complex.one_im] using (Complex.pos_iff.mp hpos.det_pos).2

end
end PowerConvexity
