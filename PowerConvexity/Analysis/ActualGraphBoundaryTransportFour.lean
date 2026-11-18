import PowerConvexity.Analysis.ActualGraphShearFour
import PowerConvexity.Analysis.ActualFlatCenteredGeometryFour

/-! # Actual zero boundary values and closure points in genuine graph coordinates -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_flat_boundary_point_mem_closure_radius_four {N c : E} (hN : ‖N‖=1)
    {R : ℝ} (hc : inner ℝ N c=0) (hcR : ‖c‖ < R) :
    c ∈ closure (actualFlatUpperBallFour N R) := by
  have ht : Tendsto (fun t : ℝ => c+t • N) (𝓝[>] (0 : ℝ)) (𝓝 c) := by
    have hh : ContinuousAt (fun t : ℝ => c+t • N) 0 := by fun_prop
    simpa only [zero_smul,add_zero] using hh.tendsto.mono_left nhdsWithin_le_nhds
  apply mem_closure_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds (by linarith : (0 : ℝ) < R-‖c‖))] with t ht0 htR
  have hp : 0 < t := ht0
  have htn : ‖t • N‖=t := by rw [norm_smul,Real.norm_eq_abs,abs_of_pos hp,hN,mul_one]
  refine ⟨?_,?_⟩
  · rw [mem_ball,dist_zero_right]
    have hh := norm_add_le c (t • N)
    rw [htn] at hh
    change t < R-‖c‖ at htR
    linarith
  · change 0 < inner ℝ N (c+t • N)
    simpa only [inner_add_right,hc,inner_smul_right,real_inner_self_eq_norm_sq,hN,one_pow,mul_one,zero_add] using hp

theorem actual_graph_flat_boundary_frontier_four {U : Set E} (hU : IsOpen U)
    {x N c : E} (hN : ‖N‖=1) {rho : E → ℝ} {R : ℝ}
    (hrho : ContinuousAt rho c) (hc : inner ℝ N c=0) (hcR : ‖c‖ < R)
    (hmap : ∀ z ∈ closedBall (0 : E) R,
      x+actualGraphShearFour N rho z ∈ U ↔ 0 < inner ℝ N z) :
    x+actualGraphShearFour N rho c ∈ frontier U := by
  have hcont : ContinuousAt (fun z : E => x+actualGraphShearFour N rho z) c :=
    continuousAt_const.add (continuousAt_id.add (hrho.smul continuousAt_const))
  have hmapU : MapsTo (fun z : E => x+actualGraphShearFour N rho z) (actualFlatUpperBallFour N R) U := by
    intro z hz
    exact (hmap z (ball_subset_closedBall hz.1)).mpr hz.2
  have hcl := hcont.continuousWithinAt.mem_closure
    (actual_flat_boundary_point_mem_closure_radius_four hN hc hcR) hmapU
  rw [hU.frontier_eq]
  refine ⟨hcl,?_⟩
  intro hin
  have hh := (hmap c (by simpa only [mem_closedBall,dist_zero_right] using hcR.le)).mp hin
  rw [hc] at hh
  exact lt_irrefl 0 hh

theorem actual_graph_zero_boundary_transport_four {U : Set E} (hU : IsOpen U)
    {x N : E} (hN : ‖N‖=1) {rho u : E → ℝ} {R : ℝ}
    (hR : 0 < R) (hrho : ∀ c ∈ ball (0 : E) R, ContinuousAt rho c)
    (hmap : ∀ z ∈ closedBall (0 : E) R,
      x+actualGraphShearFour N rho z ∈ U ↔ 0 < inner ℝ N z)
    (hu : ∀ y ∈ frontier U, u y=0) :
    ∀ z ∈ closedBall (0 : E) (R/2), inner ℝ N z=0 →
      u (x+actualGraphShearFour N rho z)=0 := by
  intro z hz hNz
  have hzR : ‖z‖ < R := (show ‖z‖ ≤ R/2 from by simpa only [mem_closedBall,dist_zero_right] using hz).trans_lt (by linarith)
  exact hu _ (actual_graph_flat_boundary_frontier_four hU hN
    (hrho z (by simpa only [mem_ball,dist_zero_right] using hzR)) hNz hzR hmap)

end PowerConvexity
