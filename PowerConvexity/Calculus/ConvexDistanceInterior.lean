import PowerConvexity.Calculus.DistanceInteriorTruncation
import Mathlib.Analysis.Convex.Topology

/-! # Convexity and nonemptiness of the frozen distance interior -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric
open scoped Topology
namespace PowerConvexity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem infDist_frontier_eq_compl_of_mem
    {U : Set E} (hU : IsOpen U) (hproper : U ≠ univ) {x : E} (hx : x ∈ U) :
    infDist x (frontier U) = infDist x Uᶜ := by
  obtain ⟨y,hy,he⟩ := exists_mem_frontier_infDist_compl_eq_dist hx hproper
  apply le_antisymm
  · exact (infDist_le_dist_of_mem hy).trans_eq he.symm
  · apply infDist_le_infDist_of_subset _ ⟨y,hy⟩
    intro z hz
    rw [hU.frontier_eq] at hz
    exact hz.2

theorem distanceInteriorDomain_convex
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hproper : U ≠ univ) (ε : ℝ) :
    Convex ℝ (distanceInteriorDomain U ε) := by
  intro x hx y hy a b ha hb hab
  let z := a • x+b • y
  have hz : z ∈ U := hconv hx.1 hy.1 ha hb hab
  have hxD : ε < infDist x Uᶜ := by
    rw [← infDist_frontier_eq_compl_of_mem hU hproper hx.1]
    exact hx.2
  have hyD : ε < infDist y Uᶜ := by
    rw [← infDist_frontier_eq_compl_of_mem hU hproper hy.1]
    exact hy.2
  let r := min (infDist x Uᶜ) (infDist y Uᶜ)
  have hr : ε < r := lt_min hxD hyD
  have hxB : ball x r ⊆ U :=
    (ball_subset_ball (min_le_left _ _)).trans ball_infDist_compl_subset
  have hyB : ball y r ⊆ U :=
    (ball_subset_ball (min_le_right _ _)).trans ball_infDist_compl_subset
  have hzB : ball z r ⊆ U := by
    intro w hw
    have hws : ‖w-z‖ < r := by simpa only [mem_ball,dist_eq_norm] using hw
    have hxw : x+(w-z) ∈ U := hxB (by
      simpa only [mem_ball,dist_eq_norm,add_sub_cancel_left] using hws)
    have hyw : y+(w-z) ∈ U := hyB (by
      simpa only [mem_ball,dist_eq_norm,add_sub_cancel_left] using hws)
    have hh := hconv hxw hyw ha hb hab
    have he : a • (x+(w-z))+b • (y+(w-z)) = w := by
      rw [smul_add,smul_add]
      calc
        a • x+a • (w-z)+(b • y+b • (w-z)) = z+(a+b) • (w-z) := by
          dsimp [z]
          module
        _ = w := by rw [hab,one_smul]; abel
    rwa [he] at hh
  have hdist : r ≤ infDist z Uᶜ := by
    apply (le_infDist (nonempty_compl.mpr hproper)).mpr
    intro w hw
    by_contra hn
    exact hw (hzB (by simpa only [mem_ball,dist_comm] using lt_of_not_ge hn))
  refine ⟨hz,?_⟩
  change ε < infDist z (frontier U)
  rw [infDist_frontier_eq_compl_of_mem hU hproper hz]
  exact hr.trans_le hdist

theorem exists_distanceInteriorDomain_nonempty_radius
    {U : Set E} (hU : IsOpen U) (hproper : U ≠ univ) (hne : U.Nonempty) :
    ∃ δ > 0, ∀ ε : ℝ, ε ≤ δ → (distanceInteriorDomain U ε).Nonempty := by
  obtain ⟨x,hx⟩ := hne
  have hd : 0 < infDist x Uᶜ :=
    (hU.isClosed_compl.notMem_iff_infDist_pos (nonempty_compl.mpr hproper)).mp (by simpa using hx)
  have hf : 0 < infDist x (frontier U) := by
    rw [infDist_frontier_eq_compl_of_mem hU hproper hx]
    exact hd
  refine ⟨infDist x (frontier U)/2,by positivity,?_⟩
  intro ε hε
  refine ⟨x,hx,?_⟩
  change ε < infDist x (frontier U)
  linarith

end PowerConvexity
