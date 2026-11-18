import PowerConvexity.Calculus.ConvexDistanceInterior
import PowerConvexity.Analysis.CompactSmallParameter

/-! # Actual distance interiors as centers of balls

For an open convex domain with an inball of radius larger than epsilon,
the closure of the manuscript's distance interior is exactly the set of
centers whose closed epsilon-ball lies in the original closure. This
description will give compact parameter graphs without homeomorphisms.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric Filter
open scoped Topology
namespace PowerConvexity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def ballCenterSet (K : Set E) (ε : ℝ) : Set E :=
  {x | ∀ z ∈ closedBall (0 : E) ε, x+z ∈ K}

theorem mem_ballCenterSet_iff {K : Set E} {ε : ℝ} {x : E} :
    x ∈ ballCenterSet K ε ↔ closedBall x ε ⊆ K := by
  constructor
  · intro hx y hy
    have hz : y-x ∈ closedBall (0 : E) ε := by
      simpa only [mem_closedBall,dist_zero_right,dist_eq_norm,sub_zero] using hy
    simpa only [add_sub_cancel] using hx (y-x) hz
  · intro hx z hz
    apply hx
    simpa only [mem_closedBall,dist_eq_norm,add_sub_cancel_left,sub_zero] using hz

theorem ballCenterSet_isClosed {K : Set E} (hK : IsClosed K) (ε : ℝ) :
    IsClosed (ballCenterSet K ε) := by
  have he : ballCenterSet K ε =
      ⋂ z : closedBall (0 : E) ε, (fun x : E => x+(z : E)) ⁻¹' K := by
    ext x
    simp only [ballCenterSet,mem_setOf_eq,mem_iInter,mem_preimage]
    exact ⟨fun h z => h z z.property,fun h z hz => h ⟨z,hz⟩⟩
  rw [he]
  exact isClosed_iInter (fun _ => hK.preimage (continuous_id.add continuous_const))

theorem ballCenterSet_convex {K : Set E} (hK : Convex ℝ K) (ε : ℝ) :
    Convex ℝ (ballCenterSet K ε) := by
  intro x hx y hy a b ha hb hab z hz
  have hh := hK (hx z hz) (hy z hz) ha hb hab
  have he : a • (x+z)+b • (y+z) = a • x+b • y+z := by
    calc
      a • (x+z)+b • (y+z) = a • x+b • y+(a+b) • z := by module
      _ = a • x+b • y+z := by rw [hab,one_smul]
  rwa [he] at hh

variable [FiniteDimensional ℝ E]

theorem distanceInteriorDomain_eq_ballCenterSet
    {U : Set E} (hU : IsOpen U) (hproper : U ≠ univ) {ε : ℝ} (hε : 0 ≤ ε) :
    distanceInteriorDomain U ε = ballCenterSet U ε := by
  ext x
  rw [mem_ballCenterSet_iff]
  constructor
  · intro hx z hz
    have hd : ε < infDist x Uᶜ := by
      rw [← infDist_frontier_eq_compl_of_mem hU hproper hx.1]
      exact hx.2
    by_contra hn
    have hh := infDist_le_dist_of_mem (show z ∈ Uᶜ from hn) (x := x)
    have hz' : dist x z ≤ ε := by simpa only [mem_closedBall,dist_comm] using hz
    exact (not_le_of_gt hd) (hh.trans hz')
  · intro hb
    have hx : x ∈ U := hb (mem_closedBall_self hε)
    refine ⟨hx,?_⟩
    change ε < infDist x (frontier U)
    rw [infDist_frontier_eq_compl_of_mem hU hproper hx]
    obtain ⟨z,hz,hd⟩ := exists_mem_frontier_infDist_compl_eq_dist hx hproper
    have hznot : z ∉ U := by rw [hU.frontier_eq] at hz; exact hz.2
    by_contra hh
    apply hznot (hb ?_)
    simpa only [mem_closedBall,dist_comm,← hd] using (le_of_not_gt hh)

theorem distanceInteriorDomain_closure_eq_ballCenterSet
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hproper : U ≠ univ)
    {ρ ε : ℝ} (hε : 0 ≤ ε) (hερ : ε < ρ)
    (hball : closedBall (0 : E) ρ ⊆ U) :
    closure (distanceInteriorDomain U ε) = ballCenterSet (closure U) ε := by
  let C := ballCenterSet (closure U) ε
  let V := distanceInteriorDomain U ε
  have hVo : IsOpen V := distanceInteriorDomain_isOpen hU ε
  have hCclosed : IsClosed C := ballCenterSet_isClosed isClosed_closure ε
  have hCconv : Convex ℝ C := ballCenterSet_convex hconv.closure ε
  have hVC : V ⊆ C := by
    rw [show V = ballCenterSet U ε from distanceInteriorDomain_eq_ballCenterSet hU hproper hε]
    exact fun x hx z hz => subset_closure (hx z hz)
  have h0V : (0 : E) ∈ V := by
    rw [show V = ballCenterSet U ε from distanceInteriorDomain_eq_ballCenterSet hU hproper hε,
      mem_ballCenterSet_iff]
    exact (closedBall_subset_closedBall hερ.le).trans hball
  have hVint : V ⊆ interior C := hVo.subset_interior_iff.mpr hVC
  have hCint : (interior C).Nonempty := ⟨0,hVint h0V⟩
  have hUne : (interior U).Nonempty := by
    rw [hU.interior_eq]
    exact ⟨0,hball (mem_closedBall_self (hε.trans hερ.le))⟩
  have hreg : interior (closure U) = U := by
    rw [hconv.interior_closure_eq_interior_of_nonempty_interior hUne,hU.interior_eq]
  have hintV : interior C ⊆ V := by
    intro x hx
    obtain ⟨δ,hδ,hδC⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
    rw [show V = ballCenterSet U ε from distanceInteriorDomain_eq_ballCenterSet hU hproper hε,
      mem_ballCenterSet_iff]
    intro z hz
    rw [← hreg]
    apply mem_interior_iff_mem_nhds.mpr
    apply Filter.mem_of_superset (ball_mem_nhds z hδ)
    intro w hw
    have hy : x+(w-z) ∈ C := hδC (by
      simpa only [mem_ball,dist_eq_norm,add_sub_cancel_left] using hw)
    apply (mem_ballCenterSet_iff.mp hy)
    have he : w-(x+(w-z)) = z-x := by abel
    simpa only [mem_closedBall,dist_eq_norm,he] using hz
  have he : V = interior C := subset_antisymm hVint hintV
  rw [show distanceInteriorDomain U ε = V from rfl,he,
    hCconv.closure_interior_eq_closure_of_nonempty_interior hCint,hCclosed.closure_eq]

end PowerConvexity
