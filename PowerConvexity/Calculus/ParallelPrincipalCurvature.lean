import PowerConvexity.Calculus.MinkowskiDefiningLeviTransport
import PowerConvexity.Analysis.ParallelCurvatureBounds

/-! # The actual parallel principal-curvature formula

The eigenvalues here belong to the derivative of the normalized actual
gradient on a genuine boundary. This identifies the scalar parallel formula
with the geometry and proves that real null directions remain null.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Filter Metric
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem definingNormal_tangent_eigenvalue_nonneg
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) {x : E} (hx : x ∈ frontier U)
    {f : E → ℝ} (hf : ContDiffAt ℝ 2 f x) (hfx : f x = 0)
    (hDf : fderiv ℝ f x ≠ 0) (hdef : ∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0)
    {v : E} (hv : v ≠ 0) (htan : fderiv ℝ f x v = 0) {κ : ℝ}
    (heig : fderiv ℝ (definingUnitNormal f) x v = κ • v) : 0 ≤ κ := by
  have hh := definingUnitNormal_tangent_form_nonneg_of_convex hU hconv hx hf hfx hDf hdef v htan
  rw [heig,real_inner_smul_left,real_inner_self_eq_norm_sq] at hh
  exact (mul_nonneg_iff_of_pos_right (sq_pos_of_pos (norm_pos_iff.mpr hv))).mp hh

theorem parallel_defining_normal_eigenvalue
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) {x : E} (hx : x ∈ frontier U)
    {f : E → ℝ} (hf : ContDiffAt ℝ 2 f x) (hfx : f x = 0)
    (hDf : fderiv ℝ f x ≠ 0) (hdef : ∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0)
    {t R : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hR : 0 < R)
    {g : E → ℝ} (hg : ContDiffAt ℝ 2 g (definingParallelMap f t ((1-t)*R) x))
    (hgy : g (definingParallelMap f t ((1-t)*R) x) = 0)
    (hDg : fderiv ℝ g (definingParallelMap f t ((1-t)*R) x) ≠ 0)
    (hgdef : ∀ᶠ z in 𝓝 (definingParallelMap f t ((1-t)*R) x),
      z ∈ minkowskiDomain t U (ball (0 : E) R) ↔ g z < 0)
    {v : E} (hv : v ≠ 0) (htan : fderiv ℝ f x v = 0) {κ : ℝ}
    (heig : fderiv ℝ (definingUnitNormal f) x v = κ • v) :
    fderiv ℝ (definingUnitNormal g) (definingParallelMap f t ((1-t)*R) x) v =
      (κ/(t+(1-t)*R*κ)) • v := by
  have hκ := definingNormal_tangent_eigenvalue_nonneg hU hconv hx hf hfx hDf hdef hv htan heig
  have hd : 0 < t+(1-t)*R*κ := add_pos_of_pos_of_nonneg ht
    (mul_nonneg (mul_nonneg (sub_nonneg.mpr ht1) hR.le) hκ)
  have hDF : fderiv ℝ (definingParallelMap f t ((1-t)*R)) x v = (t+(1-t)*R*κ) • v := by
    rw [definingParallelMap_fderiv hf hDf]
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply,heig,smul_smul,add_smul]
  have hh := definingUnitNormal_parallel_fderiv_tangent hU hconv hx hf hfx hDf hdef
    ht ht1 hR hg hgy hDg hgdef v htan
  rw [hDF,map_smul,heig] at hh
  have hscaled := congrArg (fun z : E => (t+(1-t)*R*κ)⁻¹ • z) hh
  calc
    _ = ((t+(1-t)*R*κ)⁻¹ * κ) • v := by
      simpa only [smul_smul,inv_mul_cancel₀ hd.ne',one_smul] using hscaled
    _ = _ := by
      congr 1
      rw [div_eq_mul_inv]
      exact mul_comm _ _

theorem parallel_defining_tangent_null_iff [FiniteDimensional ℝ E]
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) {x : E} (hx : x ∈ frontier U)
    {f : E → ℝ} (hf : ContDiffAt ℝ 2 f x) (hfx : f x = 0)
    (hDf : fderiv ℝ f x ≠ 0) (hdef : ∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0)
    {t R : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hR : 0 < R)
    {g : E → ℝ} (hg : ContDiffAt ℝ 2 g (definingParallelMap f t ((1-t)*R) x))
    (hgy : g (definingParallelMap f t ((1-t)*R) x) = 0)
    (hDg : fderiv ℝ g (definingParallelMap f t ((1-t)*R) x) ≠ 0)
    (hgdef : ∀ᶠ z in 𝓝 (definingParallelMap f t ((1-t)*R) x),
      z ∈ minkowskiDomain t U (ball (0 : E) R) ↔ g z < 0)
    {v : E} (hv : fderiv ℝ g (definingParallelMap f t ((1-t)*R) x) v = 0) :
    realHessian g (definingParallelMap f t ((1-t)*R) x) v v = 0 ↔ realHessian f x v v = 0 := by
  constructor
  · exact parallel_defining_tangent_hessian_null_transfer hU hconv hx hf hfx hDf hdef
      ht ht1 hR hg hgy hDg hgdef hv
  · intro hnull
    by_cases hv0 : v = 0
    · simp only [hv0,map_zero,ContinuousLinearMap.zero_apply]
    have hvold := (parallel_defining_tangent_kernel_iff hU hconv hx hf hfx hDf hdef
      ht.le ht1 hg hgy hDg hgdef v).mp hv
    have hnold := convex_defining_normal_derivative_zero_of_tangent_null hU hconv hx hf hfx hDf hdef hvold hnull
    have heig : fderiv ℝ (definingUnitNormal f) x v = (0 : ℝ) • v := by simpa only [zero_smul] using hnold
    have hnnew := parallel_defining_normal_eigenvalue hU hconv hx hf hfx hDf hdef
      ht ht1 hR hg hgy hDg hgdef hv0 hvold heig
    simp only [zero_div,zero_smul] at hnnew
    have hh := definingUnitNormal_fderiv_tangent_pair hg hDg v v hv
    rw [hnnew,inner_zero_left] at hh
    exact (div_eq_zero_iff.mp hh.symm).resolve_right
      (norm_ne_zero_iff.mpr (definingGradient_ne_zero hDg))

end PowerConvexity
