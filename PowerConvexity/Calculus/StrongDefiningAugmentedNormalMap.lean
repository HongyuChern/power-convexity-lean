import PowerConvexity.Calculus.MinkowskiJointLocalInverse

/-! # A genuine normal map remaining invertible at the ball endpoint

The added defining-value term vanishes on the actual boundary. It restores
the normal derivative when the Minkowski parameter is zero. Strict positive
real tangent curvature is used only at that endpoint, and is an explicit
geometric property of the strongly convex approximating domains.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def definingAugmentedParallelMap (f : E → ℝ) (t R : ℝ) (x : E) : E :=
  t • x+(1-t) • ((R+f x) • definingUnitNormal f x)

theorem definingAugmentedParallelMap_eq_on_zero
    {f : E → ℝ} {x : E} (hx : f x=0) (t R : ℝ) :
    definingAugmentedParallelMap f t R x=definingParallelMap f t ((1-t)*R) x := by
  simp only [definingAugmentedParallelMap,definingParallelMap,hx,add_zero,smul_smul]

theorem definingAugmentedParallelMap_joint_contDiffAt
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ ∞ f x)
    (hDf : fderiv ℝ f x≠0) (t R : ℝ) :
    ContDiffAt ℝ ∞ (fun p : ℝ × E => definingAugmentedParallelMap f p.1 R p.2) (t,x) := by
  have hn : ContDiffAt ℝ ∞ (fun p : ℝ × E => definingUnitNormal f p.2) (t,x) :=
    (definingUnitNormal_contDiffAt (n := ∞) (by simpa using hf) hDf).comp
      (t,x) contDiffAt_snd
  exact (contDiffAt_fst.smul contDiffAt_snd).add
    ((contDiffAt_const.sub contDiffAt_fst).smul
      ((contDiffAt_const.add (hf.comp (t,x) contDiffAt_snd)).smul hn))

theorem definingAugmentedParallelMap_fderiv_on_zero
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (hfx : f x=0)
    (hDf : fderiv ℝ f x≠0) (t R : ℝ) :
    fderiv ℝ (definingAugmentedParallelMap f t R) x =
      t • ContinuousLinearMap.id ℝ E+(1-t) •
        (R • fderiv ℝ (definingUnitNormal f) x+
          (fderiv ℝ f x).smulRight (definingUnitNormal f x)) := by
  have hd := ((hasFDerivAt_id (𝕜 := ℝ) x).const_smul t).add
    ((((hf.differentiableAt (by norm_num)).hasFDerivAt.const_add R).smul
      (definingUnitNormal_differentiableAt hf hDf).hasFDerivAt).const_smul (1-t))
  change HasFDerivAt (definingAugmentedParallelMap f t R) _ x at hd
  simpa only [definingAugmentedParallelMap,hfx,add_zero,add_comm] using hd.fderiv

theorem definingAugmentedParallelMap_fderiv_injective
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (hfx : f x=0)
    (hDf : fderiv ℝ f x≠0)
    (hcurv : ∀ v : E, fderiv ℝ f x v=0 → v≠0 →
      0 < inner ℝ (fderiv ℝ (definingUnitNormal f) x v) v)
    {t R : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (hR : 0 < R) :
    Function.Injective (fderiv ℝ (definingAugmentedParallelMap f t R) x) := by
  have hgrad : 0 < ‖gradient f x‖ := norm_pos_iff.mpr (definingGradient_ne_zero hDf)
  have hnu : inner ℝ (gradient f x) (definingUnitNormal f x)=‖gradient f x‖ := by
    rw [definingUnitNormal,inner_smul_right,real_inner_self_eq_norm_sq]
    field_simp
  have hcoef : 0 < t+(1-t)*‖gradient f x‖ := by
    by_cases ht0 : t=0
    · simpa only [ht0,sub_zero,one_mul,zero_add] using hgrad
    · exact add_pos_of_pos_of_nonneg (lt_of_le_of_ne ht (Ne.symm ht0))
        (mul_nonneg (sub_nonneg.mpr ht1) hgrad.le)
  have hker : ∀ v : E, fderiv ℝ (definingAugmentedParallelMap f t R) x v=0 → v=0 := by
    intro v hv
    rw [definingAugmentedParallelMap_fderiv_on_zero hf hfx hDf] at hv
    change t • v+(1-t) •
      (R • fderiv ℝ (definingUnitNormal f) x v+
        fderiv ℝ f x v • definingUnitNormal f x)=0 at hv
    have hnormal := congrArg (fun z : E => inner ℝ (gradient f x) z) hv
    simp only [inner_add_right,inner_smul_right,inner_gradient_left,
      definingUnitNormal_fderiv_normal_orthogonal hf hDf,mul_zero,zero_add,
      hnu,inner_zero_right] at hnormal
    have htan : fderiv ℝ f x v=0 := by nlinarith
    simp only [htan,zero_smul,add_zero] at hv
    by_contra hv0
    have hp := hcurv v htan hv0
    have hpair := congrArg (fun z : E => inner ℝ z v) hv
    simp only [inner_add_left,real_inner_smul_left,real_inner_self_eq_norm_sq,
      inner_zero_left] at hpair
    by_cases ht0 : t=0
    · simp only [ht0,zero_mul,sub_zero,one_mul,zero_add] at hpair
      exact (ne_of_gt (mul_pos hR hp)) hpair
    · have htp : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
      have hn : 0 < ‖v‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hv0)
      nlinarith [mul_nonneg (sub_nonneg.mpr ht1) (mul_nonneg hR.le hp.le)]
  intro v w hvw
  have hz : fderiv ℝ (definingAugmentedParallelMap f t R) x (v-w)=0 := by
    rw [map_sub,hvw,sub_self]
  exact sub_eq_zero.mp (hker (v-w) hz)

theorem definingAugmentedParallelMap_exists_joint_smooth_localInverse
    [FiniteDimensional ℝ E] {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (hfx : f x=0) (hDf : fderiv ℝ f x≠0)
    (hcurv : ∀ v : E, fderiv ℝ f x v=0 → v≠0 →
      0 < inner ℝ (fderiv ℝ (definingUnitNormal f) x v) v)
    {t R : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (hR : 0 < R) :
    ∃ g : ℝ × E → E,
      ContDiffAt ℝ ∞ g (t,definingAugmentedParallelMap f t R x) ∧
      g (t,definingAugmentedParallelMap f t R x)=x ∧
      (∀ᶠ p in 𝓝 (t,definingAugmentedParallelMap f t R x),
        definingAugmentedParallelMap f p.1 R (g p)=p.2) ∧
      (∀ᶠ p in 𝓝 (t,x),
        g (p.1,definingAugmentedParallelMap f p.1 R p.2)=p.2) := by
  apply exists_parameter_preserving_smooth_localInverse
    (definingAugmentedParallelMap_joint_contDiffAt hf hDf t R)
  exact definingAugmentedParallelMap_fderiv_injective ((contDiffAt_infty.mp hf) 2)
    hfx hDf hcurv ht ht1 hR

end PowerConvexity
