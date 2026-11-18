import PowerConvexity.Analysis.ActualInwardDefiningGraphFour
import PowerConvexity.Analysis.ActualGraphBoundaryTransportFour

/-! # Actual regular boundary charts with regularity on a physical ball and zero trace -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_regular_boundary_chart_four {U : Set E} (hU : IsOpen U)
    {x : E} {f u : E → ℝ} (hf : ContDiffAt ℝ 3 f x) (hf0 : f x=0)
    (hDf : fderiv ℝ f x ≠ 0)
    (hdef : ∀ᶠ y : E in 𝓝 x, y ∈ U ↔ f y < 0)
    (hu : ∀ y ∈ frontier U, u y=0) :
    ∃ N : E, ‖N‖=1 ∧ ∃ rho : E → ℝ, rho 0=0 ∧ fderiv ℝ rho 0=0 ∧
      (∀ y : E, ∀ t : ℝ, rho (y+t • N)=rho y) ∧
      ∃ R > 0, R ≤ 1 ∧ (∀ z ∈ closedBall (0 : E) R, ContDiffAt ℝ 3 rho z) ∧
        (∀ z ∈ closedBall (0 : E) R,
          x+actualGraphShearFour N rho z ∈ U ↔ 0 < inner ℝ N z) ∧
        (∀ z ∈ closedBall (0 : E) (R/2), inner ℝ N z=0 →
          x+actualGraphShearFour N rho z ∈ frontier U) ∧
        (∀ z ∈ closedBall (0 : E) (R/2), inner ℝ N z=0 →
          u (x+actualGraphShearFour N rho z)=0) := by
  obtain ⟨N,hN,rho,hrho,hrho0,hD0,hinv,S,hS,hS1,hmapS⟩ :=
    actual_inward_defining_graph_four hf hf0 hDf hdef
  have hnear : ∀ᶠ z : E in 𝓝 0, ContDiffAt ℝ 3 rho z := hrho.eventually (by norm_num)
  obtain ⟨d,hd,hball⟩ := Metric.mem_nhds_iff.mp hnear
  let R := min S (d/2)
  have hR : 0 < R := lt_min hS (half_pos hd)
  have hRS : R ≤ S := min_le_left _ _
  have hC (z : E) (hz : z ∈ closedBall 0 R) : ContDiffAt ℝ 3 rho z := by
    apply hball
    have hzR : dist z 0 ≤ R := hz
    have hRd : R ≤ d/2 := min_le_right _ _
    change dist z 0 < d
    linarith
  have hmap (z : E) (hz : z ∈ closedBall 0 R) :
      x+actualGraphShearFour N rho z ∈ U ↔ 0 < inner ℝ N z :=
    hmapS z (closedBall_subset_closedBall hRS hz)
  have hfront (z : E) (hz : z ∈ closedBall 0 (R/2)) (hNz : inner ℝ N z=0) :
      x+actualGraphShearFour N rho z ∈ frontier U := by
    have hzR : ‖z‖ < R := (show ‖z‖ ≤ R/2 from by
      simpa only [mem_closedBall,dist_zero_right] using hz).trans_lt (by linarith)
    have hzcl : z ∈ closedBall (0 : E) R := by
      simpa only [mem_closedBall,dist_zero_right] using hzR.le
    exact actual_graph_flat_boundary_frontier_four hU hN (hC z hzcl).continuousAt hNz hzR hmap
  refine ⟨N,hN,rho,hrho0,hD0,hinv,R,hR,hRS.trans hS1,hC,hmap,hfront,?_⟩
  intro z hz hNz
  exact hu _ (hfront z hz hNz)

end PowerConvexity
