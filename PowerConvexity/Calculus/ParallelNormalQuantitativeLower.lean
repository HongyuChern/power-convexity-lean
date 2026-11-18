import PowerConvexity.Calculus.MinkowskiNearZeroCurvatureUpper
import PowerConvexity.Analysis.PositiveParallelOperator

/-! # Quantitative lower comparison for the actual parallel unit normal.
The old normal derivative is the actual Frechet derivative. Its real null
directions are allowed. The comparison constant is independent of t in (0,1].
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter Metric
open scoped ContDiff Topology RealInnerProductSpace
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

theorem parallel_defining_normal_tangent_quantitative_lower
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) {x : E} (hx : x ∈ frontier U)
    {f : E → ℝ} (hf : ContDiffAt ℝ 2 f x) (hfx : f x = 0)
    (hDf : fderiv ℝ f x ≠ 0) (hdef : ∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0)
    {M : ℝ} (hM : 0 < M) (hMS : ‖fderiv ℝ (definingUnitNormal f) x‖ ≤ M)
    {t R : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hR : 0 < R)
    {g : E → ℝ} (hg : ContDiffAt ℝ 2 g (definingParallelMap f t ((1-t)*R) x))
    (hgy : g (definingParallelMap f t ((1-t)*R) x) = 0)
    (hDg : fderiv ℝ g (definingParallelMap f t ((1-t)*R) x) ≠ 0)
    (hgdef : ∀ᶠ z in 𝓝 (definingParallelMap f t ((1-t)*R) x),
      z ∈ minkowskiDomain t U (ball (0 : E) R) ↔ g z < 0)
    {v : E} (hv : fderiv ℝ g (definingParallelMap f t ((1-t)*R) x) v = 0) :
    inner ℝ (fderiv ℝ (definingUnitNormal f) x v) v / (1+R*M) ≤
      inner ℝ (fderiv ℝ (definingUnitNormal g) (definingParallelMap f t ((1-t)*R) x) v) v := by
  let S := fderiv ℝ (definingUnitNormal f) x
  let T : Submodule ℝ E := (fderiv ℝ f x).ker
  have hT (v : E) (_hv : v ∈ T) : S v ∈ T := by
    change fderiv ℝ f x (S v) = 0
    rw [← inner_gradient_left]
    exact definingUnitNormal_fderiv_normal_orthogonal hf hDf v
  have hsym (v : E) (hv : v ∈ T) (w : E) (hw : w ∈ T) :
      inner ℝ (S v) w = inner ℝ (S w) v := by
    change fderiv ℝ f x v = 0 at hv
    change fderiv ℝ f x w = 0 at hw
    rw [definingUnitNormal_fderiv_tangent_pair hf hDf v w hw,
      definingUnitNormal_fderiv_tangent_pair hf hDf w v hv,realHessian_symm hf v w]
  have hpos (v : E) (hv : v ∈ T) : 0 ≤ inner ℝ (S v) v :=
    definingUnitNormal_tangent_form_nonneg_of_convex hU hconv hx hf hfx hDf hdef v hv
  have hupper (v : E) (_hv : v ∈ T) : inner ℝ (S v) v ≤ M*‖v‖^2 := by
    have hi := real_inner_le_norm (S v) v
    have hn := S.le_opNorm v
    have h1 := mul_le_mul_of_nonneg_right hn (norm_nonneg v)
    have h2 := mul_le_mul_of_nonneg_right hMS (sq_nonneg ‖v‖)
    change ‖S‖*‖v‖^2 ≤ M*‖v‖^2 at h2
    nlinarith only [hi,h1,h2]
  let F := definingParallelMap f t ((1-t)*R)
  let L := fderiv ℝ F x
  have hi : Function.Injective L := definingParallelMap_fderiv_injective_of_convex
    hU hconv hx hf hfx hDf hdef ht (mul_nonneg (sub_nonneg.mpr ht1) hR.le)
  obtain ⟨w,hw⟩ := (LinearEquiv.ofInjectiveEndo L.toLinearMap hi).surjective v
  change fderiv ℝ (definingParallelMap f t ((1-t)*R)) x w = v at hw
  have hmap := hw
  rw [definingParallelMap_fderiv hf hDf] at hmap
  change t • w+((1-t)*R) • S w = v at hmap
  have hvold := (parallel_defining_tangent_kernel_iff hU hconv hx hf hfx hDf hdef
    ht.le ht1 hg hgy hDg hgdef v).mp hv
  have hfw : fderiv ℝ f x (S w) = 0 := by
    rw [← inner_gradient_left]
    exact definingUnitNormal_fderiv_normal_orthogonal hf hDf w
  have hwtan : fderiv ℝ f x w = 0 := by
    have hh := congrArg (fun z : E => fderiv ℝ f x z) hmap
    simp only [map_add,map_smul,hfw,hvold,smul_eq_mul,mul_zero,add_zero] at hh
    exact (mul_eq_zero.mp hh).resolve_left ht.ne'
  have hchain := definingUnitNormal_parallel_fderiv_tangent hU hconv hx hf hfx hDf hdef
    ht ht1 hR hg hgy hDg hgdef w hwtan
  rw [hw] at hchain
  have hlower := parallel_positive_operator_form_lower S T hT hsym hpos hM hupper
    ht.le ht1 hR.le hwtan
  rw [hmap] at hlower
  rw [hchain]
  exact hlower

theorem parallel_defining_Levi_quantitative_lower
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) {x : E} (hx : x ∈ frontier U)
    {f : E → ℝ} (hf : ContDiffAt ℝ 2 f x) (hfx : f x = 0)
    (hDf : fderiv ℝ f x ≠ 0) (hdef : ∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0)
    {M : ℝ} (hM : 0 < M) (hMS : ‖fderiv ℝ (definingUnitNormal f) x‖ ≤ M)
    {t R : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hR : 0 < R)
    {g : E → ℝ} (hg : ContDiffAt ℝ 2 g (definingParallelMap f t ((1-t)*R) x))
    (hgy : g (definingParallelMap f t ((1-t)*R) x) = 0)
    (hDg : fderiv ℝ g (definingParallelMap f t ((1-t)*R) x) ≠ 0)
    (hgdef : ∀ᶠ z in 𝓝 (definingParallelMap f t ((1-t)*R) x),
      z ∈ minkowskiDomain t U (ball (0 : E) R) ↔ g z < 0)
    (I : E → E) {v : E}
    (hv : fderiv ℝ g (definingParallelMap f t ((1-t)*R) x) v = 0)
    (hIv : fderiv ℝ g (definingParallelMap f t ((1-t)*R) x) (I v) = 0)
    {ell : ℝ}
    (hold : ell*‖v‖^2 ≤ inner ℝ (fderiv ℝ (definingUnitNormal f) x v) v+
      inner ℝ (fderiv ℝ (definingUnitNormal f) x (I v)) (I v)) :
    (ell/(1+R*M))*‖v‖^2 ≤
      (realHessian g (definingParallelMap f t ((1-t)*R) x) v v+
        realHessian g (definingParallelMap f t ((1-t)*R) x) (I v) (I v)) /
        ‖gradient g (definingParallelMap f t ((1-t)*R) x)‖ := by
  have h1 := parallel_defining_normal_tangent_quantitative_lower
    hU hconv hx hf hfx hDf hdef hM hMS ht ht1 hR hg hgy hDg hgdef hv
  have h2 := parallel_defining_normal_tangent_quantitative_lower
    hU hconv hx hf hfx hDf hdef hM hMS ht ht1 hR hg hgy hDg hgdef hIv
  rw [definingUnitNormal_fderiv_tangent_pair hg hDg v v hv] at h1
  rw [definingUnitNormal_fderiv_tangent_pair hg hDg (I v) (I v) hIv] at h2
  have hden : 0 < 1+R*M := by positivity
  have h3 := div_le_div_of_nonneg_right hold hden.le
  rw [add_div] at h3 ⊢
  have he : ell*‖v‖^2/(1+R*M) = (ell/(1+R*M))*‖v‖^2 := by ring
  rw [he] at h3
  linarith only [h1,h2,h3]

end PowerConvexity
