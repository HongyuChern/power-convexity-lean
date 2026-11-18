import PowerConvexity.Calculus.MinkowskiDefiningLeviTransport

/-! # Actual tangent curvature upper bounds near the ball parameter

The bound uses the actual parallel normal derivative for each t>0. It does
not require, or assert, a jointly C2 defining family extending to t=0.
It is a boundary geometry estimate, not a bound for a PDE solution Hessian.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Filter Metric
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem parallel_normal_pair_bounds
    (w z : E) {t r : ℝ} (ht : 0 ≤ t) (hr : 0 ≤ r)
    (hpair : 0 ≤ inner ℝ z w) :
    0 ≤ inner ℝ z (t • w+r • z) ∧
      r*inner ℝ z (t • w+r • z) ≤ ‖t • w+r • z‖^2 := by
  have hfirst : inner ℝ z (t • w+r • z) = t*inner ℝ z w+r*‖z‖^2 := by
    simp only [inner_add_right,real_inner_smul_right,real_inner_self_eq_norm_sq]
  have hid : ‖t • w+r • z‖^2-r*inner ℝ z (t • w+r • z) =
      t^2*‖w‖^2+t*r*inner ℝ z w := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right,
      real_inner_self_eq_norm_sq,real_inner_comm w z,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg ht,abs_of_nonneg hr]
    ring
  refine ⟨by rw [hfirst]; positivity,?_⟩
  have hp : 0 ≤ t^2*‖w‖^2+t*r*inner ℝ z w :=
    add_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (mul_nonneg (mul_nonneg ht hr) hpair)
  linarith

variable [CompleteSpace E] [FiniteDimensional ℝ E]

theorem parallel_defining_normal_tangent_upper
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) {x : E} (hx : x ∈ frontier U)
    {f : E → ℝ} (hf : ContDiffAt ℝ 2 f x) (hfx : f x = 0)
    (hDf : fderiv ℝ f x ≠ 0) (hdef : ∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0)
    {t R : ℝ} (ht : 0 < t) (ht1 : t < 1) (hR : 0 < R)
    {g : E → ℝ} (hg : ContDiffAt ℝ 2 g (definingParallelMap f t ((1-t)*R) x))
    (hgy : g (definingParallelMap f t ((1-t)*R) x) = 0)
    (hDg : fderiv ℝ g (definingParallelMap f t ((1-t)*R) x) ≠ 0)
    (hgdef : ∀ᶠ z in 𝓝 (definingParallelMap f t ((1-t)*R) x),
      z ∈ minkowskiDomain t U (ball (0 : E) R) ↔ g z < 0)
    {v : E} (hv : fderiv ℝ g (definingParallelMap f t ((1-t)*R) x) v = 0) :
    0 ≤ inner ℝ (fderiv ℝ (definingUnitNormal g) (definingParallelMap f t ((1-t)*R) x) v) v ∧
      inner ℝ (fderiv ℝ (definingUnitNormal g) (definingParallelMap f t ((1-t)*R) x) v) v ≤
        ‖v‖^2/((1-t)*R) := by
  let F := definingParallelMap f t ((1-t)*R)
  let L := fderiv ℝ F x
  have hr : 0 < (1-t)*R := mul_pos (sub_pos.mpr ht1) hR
  have hi : Function.Injective L := definingParallelMap_fderiv_injective_of_convex
    hU hconv hx hf hfx hDf hdef ht hr.le
  obtain ⟨w,hw⟩ := (LinearEquiv.ofInjectiveEndo L.toLinearMap hi).surjective v
  change fderiv ℝ (definingParallelMap f t ((1-t)*R)) x w = v at hw
  have hmap := hw
  rw [definingParallelMap_fderiv hf hDf] at hmap
  change t • w+((1-t)*R) • fderiv ℝ (definingUnitNormal f) x w = v at hmap
  have hvold := (parallel_defining_tangent_kernel_iff hU hconv hx hf hfx hDf hdef
    ht.le ht1.le hg hgy hDg hgdef v).mp hv
  have hfw : fderiv ℝ f x (fderiv ℝ (definingUnitNormal f) x w) = 0 := by
    rw [← inner_gradient_left]
    exact definingUnitNormal_fderiv_normal_orthogonal hf hDf w
  have hwtan : fderiv ℝ f x w = 0 := by
    have hh := congrArg (fun z : E => fderiv ℝ f x z) hmap
    simp only [map_add,map_smul,hfw,hvold,smul_eq_mul,mul_zero,add_zero] at hh
    exact (mul_eq_zero.mp hh).resolve_left ht.ne'
  have hchain := definingUnitNormal_parallel_fderiv_tangent hU hconv hx hf hfx hDf hdef
    ht ht1.le hR hg hgy hDg hgdef w hwtan
  rw [hw] at hchain
  have hpair := definingUnitNormal_tangent_form_nonneg_of_convex
    hU hconv hx hf hfx hDf hdef w hwtan
  have hbounds := parallel_normal_pair_bounds w (fderiv ℝ (definingUnitNormal f) x w)
    ht.le hr.le hpair
  rw [hmap] at hbounds
  rw [hchain]
  refine ⟨hbounds.1,(le_div_iff₀ hr).mpr ?_⟩
  simpa only [mul_comm] using hbounds.2

theorem parallel_defining_normal_tangent_upper_near_zero
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) {x : E} (hx : x ∈ frontier U)
    {f : E → ℝ} (hf : ContDiffAt ℝ 2 f x) (hfx : f x = 0)
    (hDf : fderiv ℝ f x ≠ 0) (hdef : ∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0)
    {t R : ℝ} (ht : 0 < t) (htHalf : t ≤ 1/2) (hR : 0 < R)
    {g : E → ℝ} (hg : ContDiffAt ℝ 2 g (definingParallelMap f t ((1-t)*R) x))
    (hgy : g (definingParallelMap f t ((1-t)*R) x) = 0)
    (hDg : fderiv ℝ g (definingParallelMap f t ((1-t)*R) x) ≠ 0)
    (hgdef : ∀ᶠ z in 𝓝 (definingParallelMap f t ((1-t)*R) x),
      z ∈ minkowskiDomain t U (ball (0 : E) R) ↔ g z < 0)
    {v : E} (hv : fderiv ℝ g (definingParallelMap f t ((1-t)*R) x) v = 0) :
    0 ≤ realHessian g (definingParallelMap f t ((1-t)*R) x) v v /
          ‖gradient g (definingParallelMap f t ((1-t)*R) x)‖ ∧
      realHessian g (definingParallelMap f t ((1-t)*R) x) v v /
          ‖gradient g (definingParallelMap f t ((1-t)*R) x)‖ ≤ (2/R)*‖v‖^2 := by
  have ht1 : t < 1 := by linarith
  have hh := parallel_defining_normal_tangent_upper hU hconv hx hf hfx hDf hdef
    ht ht1 hR hg hgy hDg hgdef hv
  rw [definingUnitNormal_fderiv_tangent_pair hg hDg v v hv] at hh
  refine ⟨hh.1,hh.2.trans ?_⟩
  have hr : 0 < (1-t)*R := mul_pos (sub_pos.mpr ht1) hR
  apply (div_le_iff₀ hr).mpr
  have hR0 : R ≠ 0 := hR.ne'
  have hfactor : 1 ≤ (2/R)*((1-t)*R) := by
    have he : (2/R)*((1-t)*R) = 2*(1-t) := by field_simp
    rw [he]
    linarith
  have hmul := mul_le_mul_of_nonneg_right hfactor (sq_nonneg ‖v‖)
  nlinarith

theorem minkowski_actual_tangent_curvature_upper_near_zero
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hboundary : HasC2LocalDefiningFunction U)
    {t R : ℝ} (ht : 0 < t) (htHalf : t ≤ 1/2) (hR : 0 < R)
    {y : E} (hy : y ∈ frontier (minkowskiDomain t U (ball (0 : E) R)))
    {g : E → ℝ} (hg : ContDiffAt ℝ 2 g y) (hgy : g y = 0)
    (hDg : fderiv ℝ g y ≠ 0)
    (hgdef : ∀ᶠ z in 𝓝 y, z ∈ minkowskiDomain t U (ball (0 : E) R) ↔ g z < 0)
    {v : E} (hv : fderiv ℝ g y v = 0) :
    0 ≤ realHessian g y v v/‖gradient g y‖ ∧
      realHessian g y v v/‖gradient g y‖ ≤ (2/R)*‖v‖^2 := by
  obtain ⟨x,hx,f,hf,hfx,hDf,hdef,he⟩ := minkowski_frontier_exists_parallel_normal
    hU hconv hK hboundary ht (by linarith : t < 1) hR hy
  subst y
  exact parallel_defining_normal_tangent_upper_near_zero hU hconv hx hf hfx hDf hdef
    ht htHalf hR hg hgy hDg hgdef hv

end PowerConvexity
