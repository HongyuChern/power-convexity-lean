import PowerConvexity.Calculus.DefiningParallelMap
import PowerConvexity.Analysis.MinkowskiDomainGeometry

/-! # The parallel normal map reaches the actual Minkowski boundary -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Filter Metric
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem definingUnitNormal_support_nonpos_of_convex
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) {x : E} (hx : x ∈ closure U)
    {f : E → ℝ} (hf : DifferentiableAt ℝ f x) (hfx : f x = 0)
    (hdef : ∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0) :
    ∀ y ∈ U, inner ℝ (definingUnitNormal f x) (y-x) ≤ 0 := by
  intro y hy
  have h := definingFunction_support_nonpos hU hconv hx hf hfx hdef y hy
  simpa only [definingUnitNormal,real_inner_smul_left,inner_gradient_left] using
    mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (norm_nonneg (gradient f x))) h

theorem definingParallelMap_mem_minkowski_frontier
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) {x : E} (hx : x ∈ frontier U)
    {f : E → ℝ} (hf : ContDiffAt ℝ 2 f x) (hfx : f x = 0)
    (hDf : fderiv ℝ f x ≠ 0) (hdef : ∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0)
    {t R : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hR : 0 < R) :
    definingParallelMap f t ((1-t)*R) x ∈
      frontier (minkowskiDomain t U (ball (0 : E) R)) := by
  let n := definingUnitNormal f x
  have hn : ‖n‖ = 1 := definingUnitNormal_norm hDf
  have hn0 : n ≠ 0 := by
    intro hz
    rw [hz,norm_zero] at hn
    exact zero_ne_one hn
  have hnn : inner ℝ n n = 1 := by rw [real_inner_self_eq_norm_sq,hn,one_pow]
  have hUopen : IsOpen (minkowskiDomain t U (ball (0 : E) R)) := by
    rw [minkowskiDomain_eq_smul_add]
    exact (hU.smul₀ ht.ne').add_right
  have hb : R • n ∈ closure (ball (0 : E) R) := by
    rw [closure_ball 0 hR.ne',mem_closedBall,dist_zero_right,norm_smul,
      Real.norm_eq_abs,abs_of_pos hR,hn,mul_one]
  have hc : t • x + (1-t) • (R • n) ∈
      closure (minkowskiDomain t U (ball (0 : E) R)) := by
    exact map_mem_closure₂ (f := fun a b : E => t • a+(1-t) • b)
      (by fun_prop : Continuous (fun p : E × E => t • p.1+(1-t) • p.2))
      (frontier_subset_closure hx) hb (fun a ha b hb => ⟨a,ha,b,hb,rfl⟩)
  rw [hUopen.frontier_eq]
  constructor
  · simpa only [definingParallelMap,n,smul_smul] using hc
  · rintro ⟨a,ha,b,hb,he⟩
    have hsa := strict_support_of_nonzero_normal hU hn0
      (definingUnitNormal_support_nonpos_of_convex hU hconv (frontier_subset_closure hx)
        (hf.differentiableAt (by norm_num)) hfx hdef) a ha
    rw [inner_sub_right,sub_neg] at hsa
    have hsb : inner ℝ n b ≤ R := by
      have hb' : ‖b‖ < R := by simpa only [mem_ball,dist_zero_right] using hb
      exact (real_inner_le_norm n b).trans (by simpa only [hn,one_mul] using hb'.le)
    have hs1 := mul_lt_mul_of_pos_left hsa ht
    have hs2 := mul_le_mul_of_nonneg_left hsb (sub_nonneg.mpr ht1)
    have hh := congrArg (fun z : E => inner ℝ n z) he
    change inner ℝ n (t • x+((1-t)*R) • n) = inner ℝ n (t • a+(1-t) • b) at hh
    simp only [inner_add_right,real_inner_smul_right,hnn,mul_one] at hh
    nlinarith

end PowerConvexity
