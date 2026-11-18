import PowerConvexity.Analysis.ActualBoundarySetJetErrorFour
import PowerConvexity.Calculus.ConvexDistanceInterior

/-! # The actual distance-scale ball and an actual nearest boundary point -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_boundary_distance_ball_four {U : Set E} (hU : IsOpen U) (hproper : U ≠ univ)
    {x : E} (hx : x ∈ U) :
    let d := infDist x (frontier U)
    0 < d ∧ ∃ c ∈ frontier U, ‖x-c‖=d ∧
      MapsTo (fun z : E => x+(d/4) • z) (ball (0 : E) 2) U ∧
      ∀ z ∈ ball (0 : E) 2, ‖(x+(d/4) • z)-c‖ ≤ 6*(d/4) := by
  dsimp only
  let d := infDist x (frontier U)
  have hdC : d=infDist x Uᶜ := infDist_frontier_eq_compl_of_mem hU hproper hx
  have hd : 0 < d := by
    rw [hdC]
    exact (hU.isClosed_compl.notMem_iff_infDist_pos (nonempty_compl.mpr hproper)).mp (by simpa using hx)
  obtain ⟨c,hc,hcD⟩ := exists_mem_frontier_infDist_compl_eq_dist hx hproper
  have hxc : ‖x-c‖=d := by rw [hdC,hcD,dist_eq_norm]
  refine ⟨hd,c,hc,hxc,?_,?_⟩
  · intro z hz
    apply ball_infDist_compl_subset
    rw [mem_ball,dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < d/4),← hdC]
    have hz2 : ‖z‖ < 2 := by simpa only [mem_ball,dist_zero_right] using hz
    nlinarith
  · intro z hz
    have hz2 : ‖z‖ ≤ 2 := (show ‖z‖ < 2 from by simpa only [mem_ball,dist_zero_right] using hz).le
    have he : (x+(d/4) • z)-c=(x-c)+(d/4) • z := by abel
    rw [he]
    apply (norm_add_le (x-c) ((d/4) • z)).trans
    rw [hxc,norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity : 0 < d/4)]
    nlinarith

end PowerConvexity
