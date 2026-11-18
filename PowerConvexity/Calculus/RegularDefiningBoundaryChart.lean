import PowerConvexity.Calculus.RegularLevelChart
import PowerConvexity.Calculus.DefiningFunctionInteriorBall

/-! # Genuine boundary charts from the manuscript's defining-function data -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric Filter
open scoped ContDiff Topology
namespace PowerConvexity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem regular_defining_zero_mem_frontier
    {U : Set E} (hU : IsOpen U) {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hfx : f x = 0) (hDf : fderiv ℝ f x ≠ 0)
    (hdef : ∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0) : x ∈ frontier U := by
  let N := (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x)
  have hD (v : E) : fderiv ℝ f x v = inner ℝ N v := InnerProductSpace.toDual_symm_apply.symm
  have hN : N ≠ 0 := by
    intro hz
    apply hDf
    ext v
    rw [hD,hz,inner_zero_left,ContinuousLinearMap.zero_apply]
  obtain ⟨r,hr,hball⟩ := exists_interior_ball_of_C2_defining_function hf hfx hN hD hdef
  have hR : 0 < r*‖N‖ := mul_pos hr (norm_pos_iff.mpr hN)
  have hxcl : x ∈ closure U := by
    apply closure_mono hball
    rw [closure_ball _ hR.ne',mem_closedBall,dist_eq_norm,sub_sub_cancel,norm_smul,
      Real.norm_eq_abs,abs_of_pos hr]
  rw [hU.frontier_eq]
  refine ⟨hxcl,?_⟩
  intro hxU
  have hh := hdef.self_of_nhds.mp hxU
  simpa only [hfx,lt_self_iff_false] using hh

theorem exists_contDiff_defining_boundary_chart
    {U : Set E} (hU : IsOpen U) {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hfx : f x = 0) (hDf : fderiv ℝ f x ≠ 0)
    (hdef : ∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0) :
    ∃ (γ : E → E) (N : Set E), IsOpen N ∧ (0 : E) ∈ N ∧ γ 0 = x ∧
      ContDiffOn ℝ 2 γ N ∧ MapsTo γ N (frontier U) ∧
      (∀ y ∈ N, f (γ y) = 0) ∧
      (∀ v : E, fderiv ℝ f x v = 0 → fderiv ℝ γ 0 v = v) := by
  obtain ⟨γ,hγ0,hγc,hγf,hγD⟩ := exists_contDiff_regular_level_chart hf hfx hDf
  have hmap : Tendsto γ (𝓝 (0 : E)) (𝓝 x) := by
    simpa only [hγ0] using hγc.continuousAt.tendsto
  have hnearD : ∀ᶠ y in 𝓝 x, fderiv ℝ f y ≠ 0 :=
    (hf.fderiv_right (m := 1) (by norm_num)).continuousAt.tendsto.eventually
      (eventually_ne_nhds hDf)
  have hneardef : ∀ᶠ y in 𝓝 x, ∀ᶠ z in 𝓝 y, z ∈ U ↔ f z < 0 :=
    eventually_eventually_nhds.mpr hdef
  have hnear : ∀ᶠ y in 𝓝 (0 : E), ContDiffAt ℝ 2 γ y ∧ γ y ∈ frontier U ∧ f (γ y) = 0 := by
    filter_upwards [hγc.eventually (by norm_num), hγf,
      hmap.eventually (hf.eventually (by norm_num)), hmap.eventually hnearD,
      hmap.eventually hneardef] with y hy hfy hreg hDy hdy
    exact ⟨hy,regular_defining_zero_mem_frontier hU hreg hfy hDy hdy,hfy⟩
  obtain ⟨N,hN,hNo,h0N⟩ := _root_.mem_nhds_iff.mp hnear
  refine ⟨γ,N,hNo,h0N,hγ0,?_,?_,?_,hγD⟩
  · intro y hy
    exact (hN hy).1.contDiffWithinAt
  · intro y hy
    exact (hN hy).2.1
  · intro y hy
    exact (hN hy).2.2

end PowerConvexity
