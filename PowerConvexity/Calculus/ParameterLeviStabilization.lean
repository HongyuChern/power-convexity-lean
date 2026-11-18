import PowerConvexity.Calculus.LeviDefiningStabilization
import PowerConvexity.Calculus.ParameterFiberDerivative

/-! # A single normal correction on a parameter-space neighborhood

The correction coefficient is chosen at the base point. Actual joint Hessian
continuity then preserves full paired positivity on one common neighborhood.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter Metric
open scoped ContDiff Topology
namespace PowerConvexity
noncomputable section
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
local instance plsDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance plsDualModule : Module ℝ (E →L[ℝ] ℝ) :=
  (inferInstance : NormedSpace ℝ (E →L[ℝ] ℝ)).toModule
local instance plsDualTopology : TopologicalSpace (E →L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance plsHessAddGroup : AddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ)).toAddCommGroup
local instance plsHessSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance plsHessModule : Module ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  (inferInstance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ)).toModule
local instance plsHessTopology : TopologicalSpace (E →L[ℝ] E →L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace

theorem exists_parameter_smooth_defining_positive_pair
    (I : E →L[ℝ] E) {V : ℝ → Set E} {S : Set ℝ}
    {F : ℝ × E → ℝ} {s : ℝ} {x : E}
    (hF : ContDiffAt ℝ ∞ F (s,x)) (hFx : F (s,x) = 0)
    (hDf : fderiv ℝ (fun y => F (s,y)) x ≠ 0)
    (hdef : ∀ᶠ p in 𝓝 (s,x), p.1 ∈ S → (p.2 ∈ V p.1 ↔ F p < 0))
    (hLevi : ∀ v : E, v ≠ 0 → fderiv ℝ (fun y => F (s,y)) x v = 0 →
      fderiv ℝ (fun y => F (s,y)) x (I v) = 0 →
      0 < realHessian (fun y => F (s,y)) x v v+
        realHessian (fun y => F (s,y)) x (I v) (I v)) :
    ∃ rho : ℝ × E → ℝ,
      ContDiffAt ℝ ∞ rho (s,x) ∧ rho (s,x) = 0 ∧
      fderiv ℝ (fun y => rho (s,y)) x = fderiv ℝ (fun y => F (s,y)) x ∧
      (∀ᶠ p in 𝓝 (s,x),
        fderiv ℝ (fun y => rho (p.1,y)) p.2 ≠ 0 ∧
        (p.1 ∈ S → (p.2 ∈ V p.1 ↔ rho p < 0)) ∧
        ∀ v : E, v ≠ 0 →
          0 < realHessian (fun y => rho (p.1,y)) p.2 v v+
            realHessian (fun y => rho (p.1,y)) p.2 (I v) (I v)) := by
  let f : E → ℝ := fun y => F (s,y)
  have hf : ContDiffAt ℝ ∞ f x := hF.comp x (contDiffAt_const.prodMk contDiffAt_id)
  have hf2 : ContDiffAt ℝ 2 f x := (contDiffAt_infty.mp hf) 2
  have hfx : f x = 0 := hFx
  obtain ⟨lam,hlam,hpos⟩ := exists_positive_normal_pair_stabilization I
    (realHessian f x) (fderiv ℝ f x) hLevi
  let rho : ℝ × E → ℝ := fun p => F p+(lam/2)*(F p*F p)
  have hrho : ContDiffAt ℝ ∞ rho (s,x) := hF.add (contDiffAt_const.mul (hF.mul hF))
  have hrho2 : ContDiffAt ℝ 2 rho (s,x) := (contDiffAt_infty.mp hrho) 2
  have hdf := hf2.differentiableAt (by norm_num)
  have hdrho : fderiv ℝ (fun y => rho (s,y)) x = fderiv ℝ f x := by
    have hprod : DifferentiableAt ℝ (fun y => f y*f y) x := hdf.fun_mul hdf
    have hmul : DifferentiableAt ℝ (fun y => (lam/2)*(f y*f y)) x := hprod.const_mul (lam/2)
    change fderiv ℝ (fun y => f y+(lam/2)*(f y*f y)) x = _
    rw [fderiv_fun_add hdf hmul,fderiv_const_mul hprod,fderiv_fun_mul hdf hdf,hfx]
    simp
  have hDrho : fderiv ℝ (fun y => rho (s,y)) x ≠ 0 := by
    rw [hdrho]
    exact hDf
  have hDnear := parameter_fiber_fderiv_eventually_ne_zero hrho2 hDrho
  have hcoef : ∀ᶠ p in 𝓝 (s,x), 0 < 1+(lam/2)*F p :=
    (continuousAt_const.add (continuousAt_const.mul hF.continuousAt)).tendsto.eventually
      (lt_mem_nhds (by rw [hFx]; norm_num : (0 : ℝ) < 1+(lam/2)*F (s,x)))
  have hrdef : ∀ᶠ p in 𝓝 (s,x), p.1 ∈ S → (p.2 ∈ V p.1 ↔ rho p < 0) := by
    filter_upwards [hdef,hcoef] with p hp hc
    intro hpS
    rw [hp hpS]
    have he : rho p = F p*(1+(lam/2)*F p) := by dsimp only [rho]; ring
    rw [he]
    constructor
    · intro hn
      exact mul_neg_of_neg_of_pos hn hc
    · intro hn
      by_contra! hnn
      exact (not_lt_of_ge (mul_nonneg hnn hc.le)) hn
  have hrpos : ∀ v : E, v ≠ 0 →
      0 < pairedBilinearForm I (realHessian (fun y => rho (s,y)) x) v v := by
    intro v hv
    rw [pairedBilinearForm_apply]
    change 0 < realHessian (fun y => f y+(lam/2)*(f y*f y)) x v v+
      realHessian (fun y => f y+(lam/2)*(f y*f y)) x (I v) (I v)
    rw [realHessian_defining_normal_correction hf2 hfx,
      realHessian_defining_normal_correction hf2 hfx]
    have hh := hpos v hv
    nlinarith
  have hD : ContDiffAt ℝ 1
      (fun p : ℝ × E => fderiv ℝ (fun y => rho (p.1,y)) p.2) (s,x) :=
    parameter_fiber_fderiv_contDiffAt (n := 1) hrho2
  have hH : ContinuousAt
      (fun p : ℝ × E => realHessian (fun y => rho (p.1,y)) p.2) (s,x) :=
    (parameter_fiber_fderiv_contDiffAt (n := 0) hD).continuousAt
  have hQ : ContinuousAt
      (fun p : ℝ × E => pairedBilinearForm I (realHessian (fun y => rho (p.1,y)) p.2))
      (s,x) := by
    unfold pairedBilinearForm
    exact hH.add (continuousAt_const.clm_comp (hH.clm_comp continuousAt_const))
  have hn := hQ.tendsto.eventually (isOpen_positive_bilinear_forms.mem_nhds hrpos)
  refine ⟨rho,hrho,by simp only [rho,hFx,mul_zero,add_zero],hdrho,?_⟩
  filter_upwards [hDnear,hrdef,hn] with p hDp hdefp hpp
  exact ⟨hDp,hdefp,hpp⟩

end
end PowerConvexity
