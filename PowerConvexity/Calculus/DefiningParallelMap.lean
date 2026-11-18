import PowerConvexity.Calculus.DefiningUnitNormal
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # The actual parallel normal map

Its derivative is injective at a convex boundary for positive dilation and
nonnegative outward displacement, even when real tangent curvature vanishes.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Filter
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem definingUnitNormal_contDiffAt {n : ℕ∞ω} {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ (n+1) f x) (hDf : fderiv ℝ f x ≠ 0) :
    ContDiffAt ℝ n (definingUnitNormal f) x := by
  have hg : ContDiffAt ℝ n (gradient f) x := by
    unfold gradient
    exact (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.contDiffAt.comp x
      (hf.fderiv_right le_rfl)
  have hn := definingGradient_ne_zero hDf
  exact ((hg.norm ℝ hn).inv (norm_ne_zero_iff.mpr hn)).smul hg

noncomputable def definingParallelMap (f : E → ℝ) (t r : ℝ) (y : E) : E :=
  t • y + r • definingUnitNormal f y

theorem definingParallelMap_contDiffAt {n : ℕ∞ω} {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ (n+1) f x) (hDf : fderiv ℝ f x ≠ 0) (t r : ℝ) :
    ContDiffAt ℝ n (definingParallelMap f t r) x := by
  exact (contDiffAt_id.const_smul t).add
    ((definingUnitNormal_contDiffAt hf hDf).const_smul r)

theorem definingParallelMap_fderiv {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hDf : fderiv ℝ f x ≠ 0) (t r : ℝ) :
    fderiv ℝ (definingParallelMap f t r) x =
      t • ContinuousLinearMap.id ℝ E + r • fderiv ℝ (definingUnitNormal f) x := by
  exact ((hasFDerivAt_id (𝕜 := ℝ) x).const_smul t |>.add
    ((definingUnitNormal_differentiableAt hf hDf).hasFDerivAt.const_smul r)).fderiv

theorem definingParallelMap_fderiv_injective_of_convex
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) {x : E} (hx : x ∈ frontier U)
    {f : E → ℝ} (hf : ContDiffAt ℝ 2 f x) (hfx : f x = 0)
    (hDf : fderiv ℝ f x ≠ 0) (hdef : ∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0)
    {t r : ℝ} (ht : 0 < t) (hr : 0 ≤ r) :
    Function.Injective (fderiv ℝ (definingParallelMap f t r) x) := by
  have hker : ∀ v : E, fderiv ℝ (definingParallelMap f t r) x v = 0 → v = 0 := by
    intro v hv
    rw [definingParallelMap_fderiv hf hDf] at hv
    change t • v + r • fderiv ℝ (definingUnitNormal f) x v = 0 at hv
    have hnorm := congrArg (fun z : E => inner ℝ (gradient f x) z) hv
    simp only [inner_add_right,inner_smul_right,inner_gradient_left,
      definingUnitNormal_fderiv_normal_orthogonal hf hDf,mul_zero,add_zero,
      inner_zero_right] at hnorm
    have htan : fderiv ℝ f x v = 0 := (mul_eq_zero.mp hnorm).resolve_left ht.ne'
    have hnn := definingUnitNormal_tangent_form_nonneg_of_convex hU hconv hx hf hfx hDf hdef v htan
    have hpair := congrArg (fun z : E => inner ℝ z v) hv
    simp only [inner_add_left,real_inner_smul_left,real_inner_self_eq_norm_sq,
      inner_zero_left] at hpair
    by_contra hv0
    have hp : 0 < t * ‖v‖^2 := mul_pos ht (sq_pos_of_pos (norm_pos_iff.mpr hv0))
    nlinarith [mul_nonneg hr hnn]
  intro v w hvw
  have hz : fderiv ℝ (definingParallelMap f t r) x (v-w) = 0 := by
    rw [map_sub,hvw,sub_self]
  exact sub_eq_zero.mp (hker (v-w) hz)

theorem definingParallelMap_exists_contDiff_localInverse_of_convex [FiniteDimensional ℝ E]
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) {x : E} (hx : x ∈ frontier U)
    {f : E → ℝ} (hf : ContDiffAt ℝ 3 f x) (hfx : f x = 0)
    (hDf : fderiv ℝ f x ≠ 0) (hdef : ∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0)
    {t r : ℝ} (ht : 0 < t) (hr : 0 ≤ r) :
    ∃ G : E → E,
      ContDiffAt ℝ 2 G (definingParallelMap f t r x) ∧
      G (definingParallelMap f t r x) = x ∧
      (∀ᶠ y in 𝓝 (definingParallelMap f t r x), definingParallelMap f t r (G y) = y) ∧
      (∀ᶠ z in 𝓝 x, G (definingParallelMap f t r z) = z) := by
  let F := definingParallelMap f t r
  let L := fderiv ℝ F x
  have hi : Function.Injective L :=
    definingParallelMap_fderiv_injective_of_convex hU hconv hx (hf.of_le (by norm_num)) hfx hDf hdef ht hr
  let e : E ≃L[ℝ] E := (LinearEquiv.ofInjectiveEndo L.toLinearMap hi).toContinuousLinearEquiv
  have he : (e : E →L[ℝ] E) = L := by ext v; rfl
  have hF : ContDiffAt ℝ 2 F x := definingParallelMap_contDiffAt hf hDf t r
  have hFd : HasFDerivAt F (e : E →L[ℝ] E) x := by
    rw [he]
    exact (hF.differentiableAt (by norm_num)).hasFDerivAt
  let G := hF.localInverse hFd (by norm_num)
  refine ⟨G,hF.to_localInverse hFd (by norm_num),
    hF.localInverse_apply_image hFd (by norm_num),?_,?_⟩
  · exact (hF.hasStrictFDerivAt' hFd (by norm_num)).eventually_right_inverse
  · exact (hF.hasStrictFDerivAt' hFd (by norm_num)).eventually_left_inverse

end PowerConvexity
