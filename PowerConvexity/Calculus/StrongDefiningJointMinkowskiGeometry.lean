import PowerConvexity.Calculus.StrongDefiningAugmentedNormalMap
import PowerConvexity.Calculus.MinkowskiJointDefining
import PowerConvexity.Calculus.StrongDefiningMinkowskiCurvature

/-! # Actual joint Minkowski defining functions through parameter zero

Positive real curvature is supplied by the actual strongly convex defining
function. The augmented map has the same boundary image as the original
parallel map, while its actual inverse is smooth also at the ball endpoint.
The proof identifies the true negative side of every nearby Minkowski fiber.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace Pointwise
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem augmentedMinkowskiMap_exists_joint_smooth_defining_function
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) {x : E} (hx : x ∈ frontier U)
    {f : E → ℝ} (hf : ContDiffAt ℝ ∞ f x) (hfx : f x=0)
    (hDf : fderiv ℝ f x≠0) (hdef : ∀ᶠ z in 𝓝 x, z∈U ↔ f z<0)
    (hcurv : ∀ v : E, fderiv ℝ f x v=0 → v≠0 →
      0 < inner ℝ (fderiv ℝ (definingUnitNormal f) x v) v)
    {s R : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) (hR : 0 < R) :
    ∃ phi : ℝ × E → ℝ,
      ContDiffAt ℝ ∞ phi (s,definingAugmentedParallelMap f s R x) ∧
      phi (s,definingAugmentedParallelMap f s R x)=0 ∧
      fderiv ℝ (fun y => phi (s,y)) (definingAugmentedParallelMap f s R x)≠0 ∧
      (∀ᶠ p in 𝓝 (s,definingAugmentedParallelMap f s R x),
        fderiv ℝ (fun y => phi (p.1,y)) p.2≠0 ∧
        (p.1 ∈ Icc (0 : ℝ) 1 →
          (p.2 ∈ minkowskiDomain p.1 U (ball (0 : E) R) ↔ phi p<0))) := by
  let Fs := definingAugmentedParallelMap f s R
  obtain ⟨g,hg,hgx,hFG,hGF⟩ := definingAugmentedParallelMap_exists_joint_smooth_localInverse
    hf hfx hDf hcurv hs hs1 hR
  let phi : ℝ × E → ℝ := f ∘ g
  have hphi : ContDiffAt ℝ ∞ phi (s,Fs x) := by
    have hfc : ContDiffAt ℝ ∞ f (g (s,Fs x)) := by simpa only [Fs,hgx] using hf
    exact hfc.comp (s,Fs x) hg
  have hphi0 : phi (s,Fs x)=0 := by simp only [phi,Function.comp_def,Fs,hgx,hfx]
  have hphis : ContDiffAt ℝ ∞ (fun y => phi (s,y)) (Fs x) :=
    hphi.comp (Fs x) (contDiffAt_const.prodMk contDiffAt_id)
  have hFsc : ContDiffAt ℝ ∞ Fs x :=
    (definingAugmentedParallelMap_joint_contDiffAt hf hDf s R).comp x
      (contDiffAt_const.prodMk contDiffAt_id)
  have hGFslice : ∀ᶠ z in 𝓝 x, g (s,Fs z)=z :=
    (show Tendsto (fun z : E => (s,z)) (𝓝 x) (𝓝 (s,x)) from
      (continuousAt_const.prodMk continuousAt_id).tendsto).eventually hGF
  have heq : (fun y => phi (s,y)) ∘ Fs =ᶠ[𝓝 x] f := by
    filter_upwards [hGFslice] with z hz
    change f (g (s,Fs z))=f z
    rw [hz]
  have hDphi : fderiv ℝ (fun y => phi (s,y)) (Fs x)≠0 := by
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
  have hnearD : ∀ᶠ z in 𝓝 x, fderiv ℝ f z≠0 :=
    (hf2.fderiv_right (m := 1) (by norm_num)).continuousAt.tendsto.eventually
      (eventually_ne_nhds hDf)
  have hnearValue : ∀ᶠ z in 𝓝 x, -R < f z := by
    have hh : -R < f x := by rw [hfx]; linarith
    exact hf.continuousAt.tendsto.eventually (lt_mem_nhds hh)
  have hside : ∀ᶠ p : ℝ × E in 𝓝 (s,Fs x), p.1 ∈ Icc (0 : ℝ) 1 →
      (phi p<0 → p.2 ∈ minkowskiDomain p.1 U (ball (0 : E) R)) ∧
      (phi p=0 → p.2 ∉ minkowskiDomain p.1 U (ball (0 : E) R)) := by
    filter_upwards [hmap.eventually (hf2.eventually (by norm_num)),
      hmap.eventually hnearD,hmap.eventually hdef.eventually_nhds,
      hmap.eventually hnearValue,hFG] with p hfp hDp hdefp hval hFp
    intro hpI
    constructor
    · intro hphip
      have hzU : g p ∈ U := hdefp.self_of_nhds.mpr hphip
      have hb : (R+f (g p)) • definingUnitNormal f (g p) ∈ ball (0 : E) R := by
        rw [mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,
          abs_of_pos (by linarith : 0 < R+f (g p)),definingUnitNormal_norm hDp,mul_one]
        change f (g p)<0 at hphip
        linarith
      rw [← hFp]
      exact ⟨g p,hzU,(R+f (g p)) • definingUnitNormal f (g p),hb,rfl⟩
    · intro hphip
      have hz := regular_defining_zero_mem_frontier hU hfp hphip hDp hdefp
      have hfeq : definingAugmentedParallelMap f p.1 R (g p)=
          definingParallelMap f p.1 ((1-p.1)*R) (g p) :=
        definingAugmentedParallelMap_eq_on_zero (f := f) (x := g p) hphip p.1 R
      by_cases ht0 : p.1=0
      · have hUn : U.Nonempty := closure_nonempty_iff.mp ⟨g p,frontier_subset_closure hz⟩
        rw [ht0,minkowskiDomain_zero hUn]
        have hpnorm : ‖p.2‖=R := by
          rw [← hFp,hfeq,ht0,definingParallelMap,zero_smul,sub_zero,one_mul,zero_add,
            norm_smul,Real.norm_eq_abs,abs_of_pos hR,definingUnitNormal_norm hDp,mul_one]
        simpa only [mem_ball,dist_zero_right,hpnorm,lt_self_iff_false,not_false_eq_true]
      · have hpt : 0 < p.1 := lt_of_le_of_ne hpI.1 (Ne.symm ht0)
        have hb := definingParallelMap_mem_minkowski_frontier hU hconv hz hfp hphip
          hDp hdefp hpt hpI.2 hR
        rw [← hfeq,hFp] at hb
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

theorem compact_regular_defining_normal_surjective
    {U : Set E} (hU : IsOpen U) (hK : IsCompact (closure U)) (hUn : U.Nonempty)
    {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hb : ∀ x ∈ frontier U, f x=0 ∧ fderiv ℝ f x≠0 ∧
      ∀ᶠ z in 𝓝 x, z∈U ↔ f z<0)
    {n : E} (hn : ‖n‖=1) :
    ∃ x ∈ frontier U, definingUnitNormal f x=n := by
  obtain ⟨x,hx,hm⟩ := hK.exists_isMaxOn hUn.closure
    (f := fun y : E => inner ℝ n y) (by fun_prop)
  have hs : ∀ y ∈ closure U, inner ℝ n (y-x) ≤ 0 := by
    intro y hy
    rw [inner_sub_right]
    exact sub_nonpos.mpr (hm hy)
  have hn0 : n≠0 := by intro hz; rw [hz,norm_zero] at hn; exact zero_ne_one hn
  have hxf : x ∈ frontier U := by
    rw [hU.frontier_eq]
    refine ⟨hx,?_⟩
    intro hxU
    have hh := strict_support_of_nonzero_normal hU hn0
      (fun y hy => hs y (subset_closure hy)) x hxU
    simpa only [sub_self,inner_zero_right,lt_self_iff_false] using hh
  exact ⟨x,hxf,(supporting_unit_vector_eq_definingUnitNormal hf.contDiffAt
    (hb x hxf).1 (hb x hxf).2.1 (hb x hxf).2.2 hn hs).symm⟩

theorem strong_defining_minkowski_exists_joint_smooth_defining_function
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hUn : U.Nonempty) {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (hb : ∀ x ∈ frontier U, f x=0 ∧ fderiv ℝ f x≠0 ∧
      ∀ᶠ z in 𝓝 x, z∈U ↔ f z<0)
    (hcurv : ∀ x ∈ frontier U, ∀ v : E, fderiv ℝ f x v=0 → v≠0 →
      0 < realHessian f x v v)
    {s R : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) (hR : 0 < R)
    {y : E} (hy : y ∈ frontier (minkowskiDomain s U (ball (0 : E) R))) :
    ∃ phi : ℝ × E → ℝ,
      ContDiffAt ℝ ∞ phi (s,y) ∧ phi (s,y)=0 ∧
      fderiv ℝ (fun z => phi (s,z)) y≠0 ∧
      (∀ᶠ p in 𝓝 (s,y),
        fderiv ℝ (fun z => phi (p.1,z)) p.2≠0 ∧
        (p.1 ∈ Icc (0 : ℝ) 1 →
          (p.2 ∈ minkowskiDomain p.1 U (ball (0 : E) R) ↔ phi p<0))) := by
  have hf2 : ContDiff ℝ 2 f := (contDiff_infty.mp hf) 2
  have hrep : ∃ x ∈ frontier U, y=definingAugmentedParallelMap f s R x := by
    by_cases hs0 : s=0
    · subst s
      rw [minkowskiDomain_zero hUn,frontier_ball 0 hR.ne'] at hy
      have hyR : ‖y‖=R := by simpa only [mem_sphere,dist_zero_right] using hy
      let n : E := R⁻¹ • y
      have hn : ‖n‖=1 := by
        rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hR),hyR,inv_mul_cancel₀ hR.ne']
      obtain ⟨x,hx,hnx⟩ := compact_regular_defining_normal_surjective hU hK hUn hf2 hb hn
      refine ⟨x,hx,?_⟩
      rw [definingAugmentedParallelMap_eq_on_zero (hb x hx).1,definingParallelMap,
        zero_smul,sub_zero,one_mul,zero_add,hnx]
      dsimp only [n]
      rw [smul_smul,mul_inv_cancel₀ hR.ne',one_smul]
    · obtain ⟨x,hx,he⟩ := minkowski_frontier_exists_parallel_global_defining hU hconv hK hf2 hb
        (lt_of_le_of_ne hs (Ne.symm hs0)) hs1 hR hy
      exact ⟨x,hx,by rw [definingAugmentedParallelMap_eq_on_zero (hb x hx).1]; exact he⟩
  obtain ⟨x,hx,rfl⟩ := hrep
  apply augmentedMinkowskiMap_exists_joint_smooth_defining_function hU hconv hx hf.contDiffAt
    (hb x hx).1 (hb x hx).2.1 (hb x hx).2.2
    (fun v hv hv0 => ?_) hs hs1 hR
  rw [definingUnitNormal_fderiv_tangent_pair hf2.contDiffAt (hb x hx).2.1 v v hv]
  exact div_pos (hcurv x hx v hv hv0)
    (norm_pos_iff.mpr (definingGradient_ne_zero (hb x hx).2.1))

end PowerConvexity
