import PowerConvexity.Calculus.ParallelMapMinkowskiBoundary
import Mathlib.Analysis.LocallyConvex.Separation

/-! # Every actual Minkowski boundary point has a parallel-normal representation

The proof uses the actual compact closure decomposition and a supporting
functional. No regularity of the new Minkowski boundary is assumed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter Metric
open scoped ContDiff Topology Pointwise
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem supportingFunctional_positive_defining_multiple
    {U : Set E} {x : E} {f : E → ℝ} (hf : ContDiffAt ℝ 2 f x)
    (hfx : f x = 0) (hDf : fderiv ℝ f x ≠ 0)
    (hdef : ∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0)
    (D : E →L[ℝ] ℝ) (hD : D ≠ 0)
    (hs : ∀ y ∈ closure U, D (y-x) ≤ 0) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ v : E, D v = lam * fderiv ℝ f x v := by
  let N := gradient f x
  have hN : N ≠ 0 := definingGradient_ne_zero hDf
  obtain ⟨r,hr,hball⟩ := exists_interior_ball_of_C2_defining_function hf hfx hN
    (fun v => (show inner ℝ N v = fderiv ℝ f x v from inner_gradient_left).symm) hdef
  have hR : 0 < r*‖N‖ := mul_pos hr (norm_pos_iff.mpr hN)
  have hsball : ∀ y ∈ closedBall (x-r • N) (r*‖N‖), D (y-x) ≤ 0 := by
    intro y hy
    apply hs y
    apply closure_mono hball
    rwa [closure_ball _ hR.ne']
  obtain ⟨lam,hlam,he⟩ := supportingFunctional_tangent_ball_positive_multiple D hD hN hr hsball
  refine ⟨lam,hlam,?_⟩
  intro v
  simpa only [N,inner_gradient_left] using he v

theorem supporting_unit_vector_eq_definingUnitNormal
    {U : Set E} {x : E} {f : E → ℝ} (hf : ContDiffAt ℝ 2 f x)
    (hfx : f x = 0) (hDf : fderiv ℝ f x ≠ 0)
    (hdef : ∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0)
    {n : E} (hn : ‖n‖ = 1)
    (hs : ∀ y ∈ closure U, inner ℝ n (y-x) ≤ 0) :
    n = definingUnitNormal f x := by
  have hD : innerSL ℝ n ≠ 0 := by
    intro hz
    have hh := congrArg (fun D : E →L[ℝ] ℝ => D n) hz
    simp only [innerSL_apply_apply,ContinuousLinearMap.zero_apply,
      real_inner_self_eq_norm_sq,hn,one_pow] at hh
    exact one_ne_zero hh
  obtain ⟨lam,hlam,he⟩ := supportingFunctional_positive_defining_multiple
    hf hfx hDf hdef (innerSL ℝ n) hD hs
  have hnN : n = lam • gradient f x := by
    apply ext_inner_right ℝ
    intro v
    simpa only [innerSL_apply_apply,real_inner_smul_left,inner_gradient_left] using he v
  have hnlam : lam * ‖gradient f x‖ = 1 := by
    rw [hnN,norm_smul,Real.norm_eq_abs,abs_of_pos hlam] at hn
    exact hn
  have hgn := norm_ne_zero_iff.mpr (definingGradient_ne_zero hDf)
  have hlameq : lam = ‖gradient f x‖⁻¹ := by
    apply (mul_right_cancel₀ hgn)
    rw [hnlam,inv_mul_cancel₀ hgn]
  simpa only [definingUnitNormal,hlameq] using hnN

theorem closedBall_support_maximizer_eq_unit_radius
    {n b : E} (hn : ‖n‖ = 1) {R : ℝ} (hR : 0 ≤ R)
    (hb : b ∈ closedBall (0 : E) R)
    (hs : ∀ c ∈ closedBall (0 : E) R, inner ℝ n c ≤ inner ℝ n b) :
    b = R • n := by
  have hc : R • n ∈ closedBall (0 : E) R := by
    simp only [mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg hR,hn,mul_one,le_refl]
  have hp := hs (R • n) hc
  simp only [real_inner_smul_right,real_inner_self_eq_norm_sq,hn,one_pow,mul_one] at hp
  have hb' : ‖b‖ ≤ R := by simpa only [mem_closedBall,dist_zero_right] using hb
  have hsq := norm_sub_sq_real b (R • n)
  rw [real_inner_smul_right,real_inner_comm n b,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg hR,hn,mul_one] at hsq
  have hz : ‖b-R • n‖ = 0 := by
    nlinarith [norm_nonneg b,norm_nonneg (b-R • n),sq_nonneg (R-‖b‖),mul_nonneg hR (sub_nonneg.mpr hp)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

theorem minkowski_frontier_exists_parallel_normal [FiniteDimensional ℝ E]
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hboundary : HasC2LocalDefiningFunction U)
    {t R : ℝ} (ht : 0 < t) (ht1 : t < 1) (hR : 0 < R)
    {y : E} (hy : y ∈ frontier (minkowskiDomain t U (ball (0 : E) R))) :
    ∃ x ∈ frontier U, ∃ f : E → ℝ,
      ContDiffAt ℝ 2 f x ∧ f x = 0 ∧ fderiv ℝ f x ≠ 0 ∧
      (∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0) ∧
      y = definingParallelMap f t ((1-t)*R) x := by
  let V := minkowskiDomain t U (ball (0 : E) R)
  have hVo : IsOpen V := by
    change IsOpen (minkowskiDomain t U (ball (0 : E) R))
    rw [minkowskiDomain_eq_smul_add]
    exact (hU.smul₀ ht.ne').add_right
  have hyc : y ∈ closure V := frontier_subset_closure hy
  have hyn : y ∉ V := by rw [hVo.frontier_eq] at hy; exact hy.2
  have hVn : V.Nonempty := closure_nonempty_iff.mp ⟨y,hyc⟩
  obtain ⟨D,hDV⟩ := geometric_hahn_banach_open_point
    (minkowskiDomain_convex hconv (convex_ball (0 : E) R) t) hVo hyn
  have hD : D ≠ 0 := by
    intro hz
    obtain ⟨z,hzV⟩ := hVn
    have hh := hDV z hzV
    simpa only [hz,ContinuousLinearMap.zero_apply,lt_self_iff_false] using hh
  have hDc : ∀ z ∈ closure V, D z ≤ D y := by
    exact closure_minimal (fun z hz => (hDV z hz).le)
      (isClosed_le D.continuous continuous_const)
  have hKB : IsCompact (closure (ball (0 : E) R)) := by
    rw [closure_ball 0 hR.ne']
    exact isCompact_closedBall 0 R
  have hrep := hyc
  change y ∈ closure (minkowskiDomain t U (ball (0 : E) R)) at hrep
  rw [minkowskiDomain_closure hK hKB,← minkowskiDomain_eq_smul_add] at hrep
  obtain ⟨a,ha,b,hb,hyab⟩ := hrep
  have hprod (z : E) (hz : z ∈ closure U) (c : E) (hc : c ∈ closure (ball (0 : E) R)) :
      t • z+(1-t) • c ∈ closure V := by
    change t • z+(1-t) • c ∈ closure (minkowskiDomain t U (ball (0 : E) R))
    rw [minkowskiDomain_closure hK hKB,← minkowskiDomain_eq_smul_add]
    exact ⟨z,hz,c,hc,rfl⟩
  have hDa : ∀ z ∈ closure U, D z ≤ D a := by
    intro z hz
    have hh := hDc _ (hprod z hz b hb)
    simp only [hyab,map_add,map_smul,smul_eq_mul] at hh
    exact (mul_le_mul_iff_right₀ ht).mp (by nlinarith)
  have hspos : 0 < 1-t := sub_pos.mpr ht1
  have hDb : ∀ c ∈ closure (ball (0 : E) R), D c ≤ D b := by
    intro c hc
    have hh := hDc _ (hprod a ha c hc)
    simp only [hyab,map_add,map_smul,smul_eq_mul] at hh
    exact (mul_le_mul_iff_right₀ hspos).mp (by nlinarith)
  let M := (InnerProductSpace.toDual ℝ E).symm D
  have hMD (z : E) : inner ℝ M z = D z := InnerProductSpace.toDual_symm_apply
  have hM : M ≠ 0 := by
    intro hz
    apply hD
    ext z
    rw [← hMD,hz,inner_zero_left,ContinuousLinearMap.zero_apply]
  let n := ‖M‖⁻¹ • M
  have hn : ‖n‖ = 1 := by
    change ‖‖M‖⁻¹ • M‖ = 1
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hM))]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hM)
  have hnd (z : E) : inner ℝ n z = ‖M‖⁻¹ * D z := by
    change inner ℝ (‖M‖⁻¹ • M) z = ‖M‖⁻¹ * D z
    rw [real_inner_smul_left,hMD]
  have hns : ∀ z ∈ closure U, inner ℝ n (z-a) ≤ 0 := by
    intro z hz
    rw [hnd,map_sub]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (norm_nonneg M))
      (sub_nonpos.mpr (hDa z hz))
  have hn0 : n ≠ 0 := by intro hz; rw [hz,norm_zero] at hn; exact zero_ne_one hn
  have haf : a ∈ frontier U := by
    rw [hU.frontier_eq]
    refine ⟨ha,?_⟩
    intro hau
    have hh := strict_support_of_nonzero_normal hU hn0 (fun z hz => hns z (subset_closure hz)) a hau
    simpa only [sub_self,inner_zero_right,lt_self_iff_false] using hh
  have hbcl : b ∈ closedBall (0 : E) R := by rwa [closure_ball 0 hR.ne'] at hb
  have hbmax : ∀ c ∈ closedBall (0 : E) R, inner ℝ n c ≤ inner ℝ n b := by
    intro c hc
    rw [hnd,hnd]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (norm_nonneg M))
    apply hDb c
    rwa [closure_ball 0 hR.ne']
  have hbeq := closedBall_support_maximizer_eq_unit_radius hn hR.le hbcl hbmax
  obtain ⟨f,hf,hfa,hDf,hdef⟩ := hboundary a haf
  have hnf := supporting_unit_vector_eq_definingUnitNormal hf hfa hDf hdef hn hns
  refine ⟨a,haf,f,hf,hfa,hDf,hdef,?_⟩
  simpa only [definingParallelMap,hbeq,hnf,smul_smul] using hyab

theorem parallel_support_representation_unique
    {x y nx ny : E} {t r : ℝ} (ht : 0 < t) (hr : 0 ≤ r)
    (hsx : inner ℝ nx (y-x) ≤ 0) (hsy : inner ℝ ny (x-y) ≤ 0)
    (he : t • x+r • nx = t • y+r • ny) : x = y := by
  have hm : 0 ≤ inner ℝ (nx-ny) (x-y) := by
    simp only [inner_sub_left,inner_sub_right] at hsx hsy ⊢
    linarith
  have hz : t • (x-y)+r • (nx-ny) = 0 := by
    calc
      _ = (t • x+r • nx)-(t • y+r • ny) := by module
      _ = 0 := sub_eq_zero.mpr he
  have hp := congrArg (fun z : E => inner ℝ z (x-y)) hz
  simp only [inner_add_left,real_inner_smul_left,real_inner_self_eq_norm_sq,inner_zero_left] at hp
  by_contra hxy
  have hpos : 0 < t*‖x-y‖^2 := mul_pos ht
    (sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)))
  nlinarith [mul_nonneg hr hm]

theorem definingParallelMap_boundary_representation_unique
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U)
    {x y : E} (hx : x ∈ frontier U) (hy : y ∈ frontier U)
    {f g : E → ℝ} (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g y)
    (hfx : f x = 0) (hgy : g y = 0)
    (hdef : ∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0)
    (hgdef : ∀ᶠ z in 𝓝 y, z ∈ U ↔ g z < 0)
    {t r : ℝ} (ht : 0 < t) (hr : 0 ≤ r)
    (he : definingParallelMap f t r x = definingParallelMap g t r y) : x = y := by
  have hsx : ∀ z ∈ closure U, inner ℝ (definingUnitNormal f x) (z-x) ≤ 0 := by
    change closure U ⊆ {z : E | inner ℝ (definingUnitNormal f x) (z-x) ≤ 0}
    apply closure_minimal
      (definingUnitNormal_support_nonpos_of_convex hU hconv (frontier_subset_closure hx)
        (hf.differentiableAt (by norm_num)) hfx hdef)
    exact isClosed_le
      (show Continuous (fun z : E => inner ℝ (definingUnitNormal f x) (z-x)) by fun_prop)
      continuous_const
  have hsy : ∀ z ∈ closure U, inner ℝ (definingUnitNormal g y) (z-y) ≤ 0 := by
    change closure U ⊆ {z : E | inner ℝ (definingUnitNormal g y) (z-y) ≤ 0}
    apply closure_minimal
      (definingUnitNormal_support_nonpos_of_convex hU hconv (frontier_subset_closure hy)
        (hg.differentiableAt (by norm_num)) hgy hgdef)
    exact isClosed_le
      (show Continuous (fun z : E => inner ℝ (definingUnitNormal g y) (z-y)) by fun_prop)
      continuous_const
  exact parallel_support_representation_unique ht hr (hsx y (frontier_subset_closure hy))
    (hsy x (frontier_subset_closure hx)) he

end PowerConvexity
