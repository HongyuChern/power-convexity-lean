import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-! # A genuine C² parametrization of a regular scalar level

The parametrization has every kernel direction in its derivative image.
It is obtained from the inverse function theorem applied to an explicit map
whose derivative at the base point is the identity.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Filter
open scoped ContDiff Topology
namespace PowerConvexity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_contDiff_regular_level_chart
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x)
    (hfx : f x = 0) (hDf : fderiv ℝ f x ≠ 0) :
    ∃ γ : E → E, γ 0 = x ∧ ContDiffAt ℝ 2 γ 0 ∧
      (∀ᶠ y in 𝓝 (0 : E), f (γ y) = 0) ∧
      ∀ v : E, fderiv ℝ f x v = 0 → fderiv ℝ γ 0 v = v := by
  let l := fderiv ℝ f x
  obtain ⟨v,hv⟩ : ∃ v : E, l v ≠ 0 := by
    by_contra! h
    apply hDf
    ext v
    exact h v
  let w := (l v)⁻¹ • v
  have hlw : l w = 1 := by
    simp only [w,map_smul,smul_eq_mul,inv_mul_cancel₀ hv]
  let P : E →L[ℝ] E := ContinuousLinearMap.id ℝ E-l.smulRight w
  have hlP (y : E) : l (P y) = 0 := by
    simp only [P,ContinuousLinearMap.sub_apply,ContinuousLinearMap.id_apply,
      ContinuousLinearMap.smulRight_apply,map_sub,map_smul,hlw,smul_eq_mul,mul_one,sub_self]
  let F : E → E := fun y => y+(f y-l (y-x)) • w
  have hF : ContDiffAt ℝ 2 F x :=
    contDiffAt_id.add ((hf.sub (l.contDiff.contDiffAt.comp x
      (contDiffAt_id.sub contDiffAt_const))).smul contDiffAt_const)
  have hFd : HasFDerivAt F (ContinuousLinearEquiv.refl ℝ E : E →L[ℝ] E) x := by
    have hid : (ContinuousLinearEquiv.refl ℝ E : E →L[ℝ] E) =
        ContinuousLinearMap.id ℝ E := by ext y; rfl
    rw [hid]
    have hs := ((hf.differentiableAt (by norm_num)).hasFDerivAt.sub
      (l.hasFDerivAt.comp x ((hasFDerivAt_id (𝕜 := ℝ) x).sub_const x))).smul_const w
    have h := (hasFDerivAt_id (𝕜 := ℝ) x).add hs
    simpa only [F,l,Pi.add_def,Pi.sub_def,Function.comp_def,id_eq,
      ContinuousLinearMap.comp_id,sub_self,ContinuousLinearMap.zero_smulRight,add_zero] using h
  have hFx : F x = x := by simp [F,hfx]
  have hrel (y : E) : l (F y-x) = f y := by
    simp only [F,show y+(f y-l (y-x)) • w-x = (y-x)+(f y-l (y-x)) • w by abel,
      map_add,map_smul,hlw,smul_eq_mul,mul_one]
    ring
  let G := hF.localInverse hFd (by norm_num)
  have hGx : G x = x := by simpa only [G,hFx] using hF.localInverse_apply_image hFd (by norm_num)
  have hGc : ContDiffAt ℝ 2 G x := by simpa only [G,hFx] using hF.to_localInverse hFd (by norm_num)
  have hGd : HasFDerivAt G (ContinuousLinearMap.id ℝ E) x := by
    have hh := (hF.hasStrictFDerivAt' hFd (by norm_num)).to_localInverse.hasFDerivAt
    have hid : ((ContinuousLinearEquiv.refl ℝ E).symm : E →L[ℝ] E) =
        ContinuousLinearMap.id ℝ E := by ext y; rfl
    rw [hid] at hh
    simpa only [G,ContDiffAt.localInverse,hFx] using hh
  have hFG : ∀ᶠ y in 𝓝 x, F (G y) = y := by
    simpa only [G,ContDiffAt.localInverse,hFx] using
      (hF.hasStrictFDerivAt' hFd (by norm_num)).eventually_right_inverse
  let γ : E → E := fun y => G (x+P y)
  have hPx : x+P 0 = x := by simp
  have hPder : HasFDerivAt (fun y => x+P y) P 0 := P.hasFDerivAt.const_add x
  have hγd : HasFDerivAt γ P 0 := by
    have hGd' : HasFDerivAt G (ContinuousLinearMap.id ℝ E) (x+P 0) := by rwa [hPx]
    simpa only [γ,Function.comp_def,ContinuousLinearMap.id_comp] using
      (hGd'.comp 0 hPder)
  refine ⟨γ,by simpa only [γ,hPx] using hGx,?_,?_,?_⟩
  · have hGc' : ContDiffAt ℝ 2 G (x+P 0) := by rwa [hPx]
    exact hGc'.comp 0 (contDiffAt_const.add P.contDiff.contDiffAt)
  · have ht : Tendsto (fun y : E => x+P y) (𝓝 0) (𝓝 x) := by
      simpa only [hPx] using hPder.continuousAt.tendsto
    filter_upwards [ht.eventually hFG] with y hy
    rw [← hrel (γ y)]
    change l (F (G (x+P y))-x) = 0
    rw [hy,add_sub_cancel_left,hlP]
  · intro y hy
    rw [hγd.fderiv]
    simp only [P,ContinuousLinearMap.sub_apply,ContinuousLinearMap.id_apply,
      ContinuousLinearMap.smulRight_apply,show l y = 0 from hy,zero_smul,sub_zero]

end PowerConvexity
