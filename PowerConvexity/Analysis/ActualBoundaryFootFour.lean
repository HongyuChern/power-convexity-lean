import PowerConvexity.Analysis.ActualBoundaryDistanceBallFour

/-! # A genuine nearest-boundary choice and its limit at every actual boundary point -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

def actualBoundaryFootOnDomainFour (U : Set E) (hproper : U ≠ univ) (x : E) : E := by
  classical
  exact if hx : x ∈ U then Classical.choose (exists_mem_frontier_infDist_compl_eq_dist hx hproper) else x

theorem actual_boundary_foot_fixed_four {U : Set E} (hU : IsOpen U) (hproper : U ≠ univ)
    {c : E} (hc : c ∈ frontier U) : actualBoundaryFootOnDomainFour U hproper c=c := by
  have hcnot : c ∉ U := by rw [hU.frontier_eq] at hc; exact hc.2
  simp only [actualBoundaryFootOnDomainFour,dif_neg hcnot]

theorem actual_boundary_foot_mem_dist_four {U : Set E} (hU : IsOpen U) (hproper : U ≠ univ)
    {x : E} (hx : x ∈ closure U) :
    actualBoundaryFootOnDomainFour U hproper x ∈ frontier U ∧
      dist x (actualBoundaryFootOnDomainFour U hproper x)=infDist x (frontier U) := by
  by_cases hxi : x ∈ U
  · have hh := Classical.choose_spec (exists_mem_frontier_infDist_compl_eq_dist hxi hproper)
    rw [actualBoundaryFootOnDomainFour,dif_pos hxi]
    exact ⟨hh.1,hh.2.symm.trans (infDist_frontier_eq_compl_of_mem hU hproper hxi).symm⟩
  · have hxf : x ∈ frontier U := by rw [hU.frontier_eq]; exact ⟨hx,hxi⟩
    rw [actualBoundaryFootOnDomainFour,dif_neg hxi]
    exact ⟨hxf,by rw [dist_self,infDist_zero_of_mem hxf]⟩

theorem actual_boundary_foot_distance_four {U : Set E} (hU : IsOpen U) (hproper : U ≠ univ)
    {x c : E} (hx : x ∈ closure U) (hc : c ∈ frontier U) :
    dist (actualBoundaryFootOnDomainFour U hproper x) c ≤ 2*dist x c := by
  have hdist := (actual_boundary_foot_mem_dist_four hU hproper hx).2
  have hle := infDist_le_dist_of_mem hc (x := x)
  calc
    dist (actualBoundaryFootOnDomainFour U hproper x) c ≤
        dist (actualBoundaryFootOnDomainFour U hproper x) x+dist x c := dist_triangle _ _ _
    _ = infDist x (frontier U)+dist x c := by rw [dist_comm _ x,hdist]
    _ ≤ 2*dist x c := by linarith

theorem actual_boundary_foot_tendsto_four {U : Set E} (hU : IsOpen U) (hproper : U ≠ univ)
    {c : E} (hc : c ∈ frontier U) :
    Tendsto (actualBoundaryFootOnDomainFour U hproper) (𝓝[closure U] c) (𝓝[frontier U] c) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · apply Metric.tendsto_nhds.mpr
    intro epsilon he
    have hb : ∀ᶠ x : E in 𝓝 c, dist x c < epsilon/2 := Metric.ball_mem_nhds c (half_pos he)
    filter_upwards [self_mem_nhdsWithin,hb.filter_mono nhdsWithin_le_nhds] with x hx hnear
    have hh := actual_boundary_foot_distance_four hU hproper hx hc
    have hd : dist x c < epsilon/2 := hnear
    linarith
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact (actual_boundary_foot_mem_dist_four hU hproper hx).1

end PowerConvexity
