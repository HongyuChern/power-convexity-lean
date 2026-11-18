import PowerConvexity.Calculus.MinkowskiBoundaryNormalRepresentation
import PowerConvexity.Calculus.ConvexLocalDefiningCriterion

/-! # Smooth defining functions for the actual intermediate Minkowski domains

The actual local inverse pulls back the old defining function. Convexity and
the intermediate value theorem identify the interior side, rather than
assuming that the new domain already has a smooth boundary.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter Metric
open scoped ContDiff Topology Pointwise
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem minkowski_mem_of_left_mem_right_closure
    {A B : Set E} (hA : IsOpen A) {t : ℝ} (ht : t ≠ 0)
    {a b : E} (ha : a ∈ A) (hb : b ∈ closure B) :
    t • a+(1-t) • b ∈ minkowskiDomain t A B := by
  rw [minkowskiDomain_eq_smul_add]
  have hb' : (1-t) • b ∈ closure ((1-t) • B) := by
    rw [closure_smul₀]
    exact ⟨b,hb,rfl⟩
  have hh : t • a+(1-t) • b ∈ t • A+closure ((1-t) • B) :=
    ⟨t • a,⟨a,ha,rfl⟩,(1-t) • b,hb',rfl⟩
  rwa [(hA.smul₀ ht).add_closure] at hh

theorem definingParallelMap_exists_smooth_localInverse_of_convex [FiniteDimensional ℝ E]
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) {x : E} (hx : x ∈ frontier U)
    {f : E → ℝ} (hf : ContDiffAt ℝ ∞ f x) (hfx : f x = 0)
    (hDf : fderiv ℝ f x ≠ 0) (hdef : ∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0)
    {t r : ℝ} (ht : 0 < t) (hr : 0 ≤ r) :
    ∃ G : E → E,
      ContDiffAt ℝ ∞ G (definingParallelMap f t r x) ∧
      G (definingParallelMap f t r x) = x ∧
      (∀ᶠ y in 𝓝 (definingParallelMap f t r x), definingParallelMap f t r (G y) = y) ∧
      (∀ᶠ z in 𝓝 x, G (definingParallelMap f t r z) = z) := by
  let F := definingParallelMap f t r
  let L := fderiv ℝ F x
  have hi : Function.Injective L :=
    definingParallelMap_fderiv_injective_of_convex hU hconv hx ((contDiffAt_infty.mp hf) 2) hfx hDf hdef ht hr
  let e : E ≃L[ℝ] E := (LinearEquiv.ofInjectiveEndo L.toLinearMap hi).toContinuousLinearEquiv
  have he : (e : E →L[ℝ] E) = L := by ext v; rfl
  have hF : ContDiffAt ℝ ∞ F x :=
    definingParallelMap_contDiffAt (n := ∞) (by simpa using hf) hDf t r
  have hFd : HasFDerivAt F (e : E →L[ℝ] E) x := by
    rw [he]
    exact (hF.differentiableAt (by norm_num)).hasFDerivAt
  let G := hF.localInverse hFd (by norm_num)
  refine ⟨G,hF.to_localInverse hFd (by norm_num),
    hF.localInverse_apply_image hFd (by norm_num),?_,?_⟩
  · exact (hF.hasStrictFDerivAt' hFd (by norm_num)).eventually_right_inverse
  · exact (hF.hasStrictFDerivAt' hFd (by norm_num)).eventually_left_inverse

theorem definingParallelMap_exists_smooth_defining_function [FiniteDimensional ℝ E]
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) {x : E} (hx : x ∈ frontier U)
    {f : E → ℝ} (hf : ContDiffAt ℝ ∞ f x) (hfx : f x = 0)
    (hDf : fderiv ℝ f x ≠ 0) (hdef : ∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0)
    {t R : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hR : 0 < R) :
    ∃ g : E → ℝ,
      ContDiffAt ℝ ∞ g (definingParallelMap f t ((1-t)*R) x) ∧
      g (definingParallelMap f t ((1-t)*R) x) = 0 ∧
      fderiv ℝ g (definingParallelMap f t ((1-t)*R) x) ≠ 0 ∧
      (∀ᶠ y in 𝓝 (definingParallelMap f t ((1-t)*R) x),
        y ∈ minkowskiDomain t U (ball (0 : E) R) ↔ g y < 0) := by
  let F := definingParallelMap f t ((1-t)*R)
  let V := minkowskiDomain t U (ball (0 : E) R)
  have hVo : IsOpen V := by
    change IsOpen (minkowskiDomain t U (ball (0 : E) R))
    rw [minkowskiDomain_eq_smul_add]
    exact (hU.smul₀ ht.ne').add_right
  have hVc : Convex ℝ V := minkowskiDomain_convex hconv (convex_ball (0 : E) R) t
  obtain ⟨G,hG,hGx,hFG,hGF⟩ := definingParallelMap_exists_smooth_localInverse_of_convex
    hU hconv hx hf hfx hDf hdef ht (mul_nonneg (sub_nonneg.mpr ht1) hR.le)
  let g := f ∘ G
  have hgc : ContDiffAt ℝ ∞ g (F x) := by
    have hfc : ContDiffAt ℝ ∞ f (G (F x)) := by simpa only [F,hGx] using hf
    exact hfc.comp (F x) hG
  have hg0 : g (F x) = 0 := by simp only [g,Function.comp_def,F,hGx,hfx]
  have hFc : ContDiffAt ℝ ∞ F x :=
    definingParallelMap_contDiffAt (n := ∞) (by simpa using hf) hDf t ((1-t)*R)
  have hgeq : g ∘ F =ᶠ[𝓝 x] f := by
    filter_upwards [hGF] with z hz
    change f (G (definingParallelMap f t ((1-t)*R) z)) = f z
    rw [hz]
  have hDg : fderiv ℝ g (F x) ≠ 0 := by
    intro hz
    have hcomp := (hgc.differentiableAt (by norm_num)).hasFDerivAt.comp x
      (hFc.differentiableAt (by norm_num)).hasFDerivAt
    have he := hgeq.fderiv_eq (𝕜 := ℝ)
    rw [hcomp.fderiv,hz,ContinuousLinearMap.zero_comp] at he
    exact hDf he.symm
  have hmap : Tendsto G (𝓝 (F x)) (𝓝 x) := by
    simpa only [F,hGx] using hG.continuousAt.tendsto
  have hf2 : ContDiffAt ℝ 2 f x := (contDiffAt_infty.mp hf) 2
  have hnearD : ∀ᶠ z in 𝓝 x, fderiv ℝ f z ≠ 0 :=
    (hf2.fderiv_right (m := 1) (by norm_num)).continuousAt.tendsto.eventually
      (eventually_ne_nhds hDf)
  have hneardef := hdef.eventually_nhds
  have hside : ∀ᶠ y in 𝓝 (F x), (g y < 0 → y ∈ V) ∧ (g y = 0 → y ∉ V) := by
    filter_upwards [hmap.eventually (hf2.eventually (by norm_num)),
      hmap.eventually hnearD,hmap.eventually hneardef,hFG] with y hfy hDy hdefy hFy
    constructor
    · intro hgy
      have hzU : G y ∈ U := hdefy.self_of_nhds.mpr hgy
      have hb : R • definingUnitNormal f (G y) ∈ closure (ball (0 : E) R) := by
        rw [closure_ball 0 hR.ne',mem_closedBall,dist_zero_right,norm_smul,
          Real.norm_eq_abs,abs_of_pos hR,definingUnitNormal_norm hDy,mul_one]
      have hh := minkowski_mem_of_left_mem_right_closure hU ht.ne' hzU hb
      rw [← hFy]
      simpa only [V,definingParallelMap,smul_smul] using hh
    · intro hgy
      have hzy := regular_defining_zero_mem_frontier hU hfy hgy hDy hdefy
      have hby := definingParallelMap_mem_minkowski_frontier hU hconv hzy hfy hgy hDy hdefy ht ht1 hR
      rw [hFy] at hby
      rw [hVo.frontier_eq] at hby
      exact hby.2
  refine ⟨g,hgc,hg0,hDg,?_⟩
  exact convex_local_defining_of_negative_side_and_zero_exclusion hVc
    ((contDiffAt_infty.mp hgc) 1) hg0 hDg (hside.mono (fun _ h => h.1)) (hside.mono (fun _ h => h.2))

theorem minkowskiDomain_hasSmoothLocalDefiningFunction [FiniteDimensional ℝ E]
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hboundary : HasSmoothLocalDefiningFunction U)
    {t R : ℝ} (ht : 0 < t) (ht1 : t < 1) (hR : 0 < R) :
    HasSmoothLocalDefiningFunction (minkowskiDomain t U (ball (0 : E) R)) := by
  intro y hy
  obtain ⟨x,hx,f,hf,hfx,hDf,hdef,hyf⟩ := minkowski_frontier_exists_parallel_normal
    hU hconv hK (smoothLocalDefiningFunction_implies_C2 hboundary) ht ht1 hR hy
  obtain ⟨g,hg,hgx,hDg,hgdef⟩ := hboundary x hx
  have hs : ∀ z ∈ closure U, inner ℝ (definingUnitNormal f x) (z-x) ≤ 0 := by
    change closure U ⊆ {z : E | inner ℝ (definingUnitNormal f x) (z-x) ≤ 0}
    exact closure_minimal
      (definingUnitNormal_support_nonpos_of_convex hU hconv (frontier_subset_closure hx)
        (hf.differentiableAt (by norm_num)) hfx hdef)
      (isClosed_le (show Continuous (fun z : E => inner ℝ (definingUnitNormal f x) (z-x)) by fun_prop)
        continuous_const)
  have hfg := supporting_unit_vector_eq_definingUnitNormal ((contDiffAt_infty.mp hg) 2) hgx hDg hgdef
    (definingUnitNormal_norm hDf) hs
  have hyg : y = definingParallelMap g t ((1-t)*R) x := by
    simpa only [definingParallelMap,hfg] using hyf
  rw [hyg]
  exact definingParallelMap_exists_smooth_defining_function hU hconv hx hg hgx hDg hgdef ht ht1.le hR

end PowerConvexity
