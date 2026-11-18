import PowerConvexity.Calculus.MinkowskiJointLocalInverse
import PowerConvexity.Calculus.ParameterConvexLocalDefining
import PowerConvexity.Calculus.ParameterFiberDerivative

/-! # Actual joint defining functions on a common parameter-space neighborhood

The original defining function is pulled back through the actual joint
normal-map inverse. The negative side and zero exclusion are identified
using the actual Minkowski domain. The uniform convex-fiber criterion then
proves the reverse implication, including at the one-sided endpoint s=1.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
open Set Filter Metric
open scoped ContDiff Topology Pointwise
namespace PowerConvexity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem definingMinkowskiParallelMap_exists_joint_smooth_defining_function
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) {x : E} (hx : x ∈ frontier U)
    {f : E → ℝ} (hf : ContDiffAt ℝ ∞ f x) (hfx : f x = 0)
    (hDf : fderiv ℝ f x ≠ 0) (hdef : ∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0)
    {s R : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hR : 0 < R) :
    ∃ phi : ℝ × E → ℝ,
      ContDiffAt ℝ ∞ phi (s,definingParallelMap f s ((1-s)*R) x) ∧
      phi (s,definingParallelMap f s ((1-s)*R) x) = 0 ∧
      fderiv ℝ (fun y => phi (s,y)) (definingParallelMap f s ((1-s)*R) x) ≠ 0 ∧
      (∀ᶠ p in 𝓝 (s,definingParallelMap f s ((1-s)*R) x),
        fderiv ℝ (fun y => phi (p.1,y)) p.2 ≠ 0 ∧
        (p.1 ∈ Icc (0 : ℝ) 1 →
          (p.2 ∈ minkowskiDomain p.1 U (ball (0 : E) R) ↔ phi p < 0))) := by
  let Fs := definingParallelMap f s ((1-s)*R)
  obtain ⟨g,hg,hgx,hFG,hGF⟩ :=
    definingMinkowskiParallelMap_exists_joint_smooth_localInverse_of_convex
      hU hconv hx hf hfx hDf hdef hs hs1 hR.le
  let phi : ℝ × E → ℝ := f ∘ g
  have hphi : ContDiffAt ℝ ∞ phi (s,Fs x) := by
    have hfc : ContDiffAt ℝ ∞ f (g (s,Fs x)) := by simpa only [Fs,hgx] using hf
    exact hfc.comp (s,Fs x) hg
  have hphi0 : phi (s,Fs x) = 0 := by simp only [phi,Function.comp_def,Fs,hgx,hfx]
  have hphis : ContDiffAt ℝ ∞ (fun y => phi (s,y)) (Fs x) :=
    hphi.comp (Fs x) (contDiffAt_const.prodMk contDiffAt_id)
  have hFsc : ContDiffAt ℝ ∞ Fs x :=
    definingParallelMap_contDiffAt (n := ∞) (by simpa using hf) hDf s ((1-s)*R)
  have hGFslice : ∀ᶠ z in 𝓝 x, g (s,Fs z) = z :=
    (show Tendsto (fun z : E => (s,z)) (𝓝 x) (𝓝 (s,x)) from
      (continuousAt_const.prodMk continuousAt_id).tendsto).eventually hGF
  have heq : (fun y => phi (s,y)) ∘ Fs =ᶠ[𝓝 x] f := by
    filter_upwards [hGFslice] with z hz
    change f (g (s,Fs z)) = f z
    rw [hz]
  have hDphi : fderiv ℝ (fun y => phi (s,y)) (Fs x) ≠ 0 := by
    intro hz
    have hc := (hphis.differentiableAt (by norm_num)).hasFDerivAt.comp x
      (hFsc.differentiableAt (by norm_num)).hasFDerivAt
    have he := heq.fderiv_eq (𝕜 := ℝ)
    rw [hc.fderiv,hz,ContinuousLinearMap.zero_comp] at he
    exact hDf he.symm
  have hphi2 : ContDiffAt ℝ 2 phi (s,Fs x) := (contDiffAt_infty.mp hphi) 2
  have hDnear := parameter_fiber_fderiv_eventually_ne_zero hphi2 hDphi
  have hmap : Tendsto g (𝓝 (s,Fs x)) (𝓝 x) := by
    simpa only [Fs,hgx] using hg.continuousAt.tendsto
  have hf2 : ContDiffAt ℝ 2 f x := (contDiffAt_infty.mp hf) 2
  have hnearD : ∀ᶠ z in 𝓝 x, fderiv ℝ f z ≠ 0 :=
    (hf2.fderiv_right (m := 1) (by norm_num)).continuousAt.tendsto.eventually
      (eventually_ne_nhds hDf)
  have hpositive : ∀ᶠ p : ℝ × E in 𝓝 (s,Fs x), 0 < p.1 :=
    continuousAt_fst.tendsto.eventually (lt_mem_nhds hs)
  have hside : ∀ᶠ p : ℝ × E in 𝓝 (s,Fs x), p.1 ∈ Icc (0 : ℝ) 1 →
      (phi p < 0 → p.2 ∈ minkowskiDomain p.1 U (ball (0 : E) R)) ∧
      (phi p = 0 → p.2 ∉ minkowskiDomain p.1 U (ball (0 : E) R)) := by
    filter_upwards [hmap.eventually (hf2.eventually (by norm_num)),
      hmap.eventually hnearD,hmap.eventually hdef.eventually_nhds,hFG,hpositive]
      with p hfp hDp hdefp hFp hpt
    intro hpI
    constructor
    · intro hphip
      have hzU : g p ∈ U := hdefp.self_of_nhds.mpr hphip
      have hb : R • definingUnitNormal f (g p) ∈ closure (ball (0 : E) R) := by
        rw [closure_ball 0 hR.ne',mem_closedBall,dist_zero_right,norm_smul,
          Real.norm_eq_abs,abs_of_pos hR,definingUnitNormal_norm hDp,mul_one]
      have hh := minkowski_mem_of_left_mem_right_closure hU hpt.ne' hzU hb
      rw [← hFp]
      simpa only [definingParallelMap,smul_smul] using hh
    · intro hphip
      have hz := regular_defining_zero_mem_frontier hU hfp hphip hDp hdefp
      have hb := definingParallelMap_mem_minkowski_frontier hU hconv hz hfp hphip
        hDp hdefp hpt hpI.2 hR
      rw [hFp] at hb
      have hVo : IsOpen (minkowskiDomain p.1 U (ball (0 : E) R)) := by
        rw [minkowskiDomain_eq_smul_add]
        exact (hU.smul₀ hpt.ne').add_right
      rw [hVo.frontier_eq] at hb
      exact hb.2
  have hcont : ∀ᶠ p in 𝓝 (s,Fs x), ContinuousAt phi p := by
    filter_upwards [hphi2.eventually (by norm_num)] with p hp
    exact hp.continuousAt
  have hdefphi := parameter_convex_local_defining_of_negative_side_and_zero_exclusion
    (fun t : ℝ => minkowskiDomain_convex hconv (convex_ball (0 : E) R) t)
    hphi0 hDphi hcont
    (hside.mono (fun _ hp hI => (hp hI).1))
    (hside.mono (fun _ hp hI => (hp hI).2))
  refine ⟨phi,hphi,hphi0,hDphi,?_⟩
  filter_upwards [hDnear,hdefphi] with p hDp hdefp
  exact ⟨hDp,hdefp⟩

theorem minkowskiDomain_exists_joint_smooth_defining_function
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hboundary : HasSmoothLocalDefiningFunction U)
    {s R : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hR : 0 < R)
    {y : E} (hy : y ∈ frontier (minkowskiDomain s U (ball (0 : E) R))) :
    ∃ phi : ℝ × E → ℝ,
      ContDiffAt ℝ ∞ phi (s,y) ∧ phi (s,y) = 0 ∧
      fderiv ℝ (fun z => phi (s,z)) y ≠ 0 ∧
      (∀ᶠ p in 𝓝 (s,y),
        fderiv ℝ (fun z => phi (p.1,z)) p.2 ≠ 0 ∧
        (p.1 ∈ Icc (0 : ℝ) 1 →
          (p.2 ∈ minkowskiDomain p.1 U (ball (0 : E) R) ↔ phi p < 0))) := by
  by_cases hslt : s < 1
  · obtain ⟨x,hx,f,hf,hfx,hDf,hdef,hyf⟩ := minkowski_frontier_exists_parallel_normal
      hU hconv hK (smoothLocalDefiningFunction_implies_C2 hboundary) hs hslt hR hy
    obtain ⟨g,hg,hgx,hDg,hgdef⟩ := hboundary x hx
    have hsupport : ∀ z ∈ closure U, inner ℝ (definingUnitNormal f x) (z-x) ≤ 0 := by
      change closure U ⊆ {z : E | inner ℝ (definingUnitNormal f x) (z-x) ≤ 0}
      exact closure_minimal
        (definingUnitNormal_support_nonpos_of_convex hU hconv (frontier_subset_closure hx)
          (hf.differentiableAt (by norm_num)) hfx hdef)
        (isClosed_le (show Continuous (fun z : E => inner ℝ (definingUnitNormal f x) (z-x)) by
          fun_prop) continuous_const)
    have hfg := supporting_unit_vector_eq_definingUnitNormal ((contDiffAt_infty.mp hg) 2)
      hgx hDg hgdef (definingUnitNormal_norm hDf) hsupport
    have hyg : y = definingParallelMap g s ((1-s)*R) x := by
      simpa only [definingParallelMap,hfg] using hyf
    rw [hyg]
    exact definingMinkowskiParallelMap_exists_joint_smooth_defining_function
      hU hconv hx hg hgx hDg hgdef hs hs1 hR
  · have hsEq : s = 1 := le_antisymm hs1 (not_lt.mp hslt)
    subst s
    have hBn : (ball (0 : E) R).Nonempty := ⟨0,mem_ball_self hR⟩
    rw [minkowskiDomain_one hBn] at hy
    obtain ⟨f,hf,hfx,hDf,hdef⟩ := hboundary y hy
    have hF1 : definingParallelMap f 1 ((1-1)*R) y = y := by
      simp [definingParallelMap]
    simpa only [hF1] using
      definingMinkowskiParallelMap_exists_joint_smooth_defining_function
        hU hconv hy hf hfx hDf hdef (by norm_num : (0 : ℝ) < 1) le_rfl hR

end PowerConvexity
