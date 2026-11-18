import PowerConvexity.Analysis.RankTwoBoundaryPositivity
import PowerConvexity.Analysis.PositiveBilinearTopology
import PowerConvexity.Calculus.RealHessianQuotient

/-! # A strictly positive Levi defining function near an actual boundary point

The normal-square correction preserves the actual boundary and the defining
gradient. Positivity is first obtained on the full ambient space, then on a
neighborhood by continuity and compactness of the unit sphere.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Filter Metric
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

noncomputable def pairedBilinearForm (I : E →L[ℝ] E) (H : E →L[ℝ] E →L[ℝ] ℝ) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  H+((ContinuousLinearMap.compL ℝ E E ℝ).flip I).comp (H.comp I)

theorem pairedBilinearForm_apply (I : E →L[ℝ] E) (H : E →L[ℝ] E →L[ℝ] ℝ)
    (v w : E) : pairedBilinearForm I H v w = H v w+H (I v) (I w) := rfl

theorem exists_positive_normal_pair_stabilization
    (I : E →L[ℝ] E) (H : E →L[ℝ] E →L[ℝ] ℝ) (D : E →L[ℝ] ℝ)
    (hker : ∀ v : E, v ≠ 0 → D v = 0 → D (I v) = 0 →
      0 < H v v+H (I v) (I v)) :
    ∃ lam > 0, ∀ v : E, v ≠ 0 →
      0 < H v v+H (I v) (I v)+lam*((D v)^2+(D (I v))^2) := by
  exact exists_rankTwo_stabilization_positive (pairedBilinearForm I H) D (D.comp I) hker

theorem realHessian_defining_normal_correction
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (hfx : f x = 0)
    (lam : ℝ) (v w : E) :
    realHessian (fun y => f y+(lam/2)*(f y*f y)) x v w =
      realHessian f x v w+lam*fderiv ℝ f x v*fderiv ℝ f x w := by
  rw [realHessian_add hf (contDiffAt_const.mul (hf.mul hf)),
    add_apply,add_apply,realHessian_const_mul_at (hf.mul hf),
    smul_apply,smul_apply,smul_eq_mul,realHessian_mul_real_at hf hf,hfx]
  ring

theorem exists_smooth_defining_positive_pair
    (I : E →L[ℝ] E) {U : Set E} {x : E} {f : E → ℝ}
    (hf : ContDiffAt ℝ ∞ f x) (hfx : f x = 0) (hDf : fderiv ℝ f x ≠ 0)
    (hdef : ∀ᶠ y in 𝓝 x, y ∈ U ↔ f y < 0)
    (hLevi : ∀ v : E, v ≠ 0 → fderiv ℝ f x v = 0 → fderiv ℝ f x (I v) = 0 →
      0 < realHessian f x v v+realHessian f x (I v) (I v)) :
    ∃ rho : E → ℝ, ContDiffAt ℝ ∞ rho x ∧ rho x = 0 ∧
      fderiv ℝ rho x = fderiv ℝ f x ∧ fderiv ℝ rho x ≠ 0 ∧
      (∀ᶠ y in 𝓝 x, y ∈ U ↔ rho y < 0) ∧
      (∀ᶠ y in 𝓝 x, ∀ v : E, v ≠ 0 →
        0 < realHessian rho y v v+realHessian rho y (I v) (I v)) := by
  letI : AddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
    (inferInstance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ)).toAddCommGroup
  letI : Module ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
    (inferInstance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ)).toModule
  letI : TopologicalSpace (E →L[ℝ] E →L[ℝ] ℝ) :=
    (inferInstance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace
  have hf2 : ContDiffAt ℝ 2 f x := (contDiffAt_infty.mp hf) 2
  obtain ⟨lam,hlam,hpos⟩ := exists_positive_normal_pair_stabilization I
    (realHessian f x) (fderiv ℝ f x) hLevi
  let rho : E → ℝ := fun y => f y+(lam/2)*(f y*f y)
  have hrho : ContDiffAt ℝ ∞ rho x := hf.add (contDiffAt_const.mul (hf.mul hf))
  have hrho2 : ContDiffAt ℝ 2 rho x := (contDiffAt_infty.mp hrho) 2
  have hdf := hf2.differentiableAt (by norm_num)
  have hdrho : fderiv ℝ rho x = fderiv ℝ f x := by
    have hprod : DifferentiableAt ℝ (fun y => f y*f y) x := hdf.fun_mul hdf
    have hmul : DifferentiableAt ℝ (fun y => (lam/2)*(f y*f y)) x := hprod.const_mul (lam/2)
    change fderiv ℝ (fun y => f y+(lam/2)*(f y*f y)) x = _
    rw [fderiv_fun_add hdf hmul,fderiv_const_mul hprod,fderiv_fun_mul hdf hdf,hfx]
    simp
  have hcoef : ∀ᶠ y in 𝓝 x, 0 < 1+(lam/2)*f y :=
    (continuousAt_const.add (continuousAt_const.mul hf.continuousAt)).tendsto.eventually
      (lt_mem_nhds (by rw [hfx]; norm_num : (0 : ℝ) < 1+(lam/2)*f x))
  have hrdef : ∀ᶠ y in 𝓝 x, y ∈ U ↔ rho y < 0 := by
    filter_upwards [hdef,hcoef] with y hy hc
    rw [hy]
    have he : rho y = f y*(1+(lam/2)*f y) := by dsimp only [rho]; ring
    rw [he]
    constructor
    · intro hn
      exact mul_neg_of_neg_of_pos hn hc
    · intro hn
      by_contra! hnn
      exact (not_lt_of_ge (mul_nonneg hnn hc.le)) hn
  have hrpos : ∀ v : E, v ≠ 0 → 0 < pairedBilinearForm I (realHessian rho x) v v := by
    intro v hv
    rw [pairedBilinearForm_apply]
    change 0 < realHessian (fun y => f y+(lam/2)*(f y*f y)) x v v+
      realHessian (fun y => f y+(lam/2)*(f y*f y)) x (I v) (I v)
    rw [realHessian_defining_normal_correction hf2 hfx,
      realHessian_defining_normal_correction hf2 hfx]
    have hh := hpos v hv
    nlinarith
  have hH : ContinuousAt (fun y => realHessian rho y) x :=
    ((hrho2.fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)).continuousAt
  have hQ : ContinuousAt (fun y => pairedBilinearForm I (realHessian rho y)) x := by
    unfold pairedBilinearForm
    exact hH.add (continuousAt_const.clm_comp (hH.clm_comp continuousAt_const))
  have hn := hQ.tendsto.eventually (isOpen_positive_bilinear_forms.mem_nhds hrpos)
  refine ⟨rho,hrho,by simp [rho,hfx],hdrho,hdrho ▸ hDf,hrdef,?_⟩
  exact hn

end PowerConvexity
