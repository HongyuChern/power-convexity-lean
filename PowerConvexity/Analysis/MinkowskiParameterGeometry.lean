import PowerConvexity.Analysis.MinkowskiDomainGeometry
import PowerConvexity.Analysis.MinkowskiInteriorStability
import PowerConvexity.Calculus.ConvexDistanceInterior

/-! # Compact parameter graphs and a common actual distance truncation

All sets are the physical Minkowski domains or the manuscript's distance
interiors. These statements do not replace strict convexity by positive
real curvature, and do not introduce a parametrizing homeomorphism.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric Filter
open scoped Topology Pointwise
namespace PowerConvexity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
local notation "T" => Icc (0 : ℝ) 1

theorem minkowskiDomain_closure_parameterGraph_isCompact
    {A B : Set E} (hAK : IsCompact (closure A)) (hBK : IsCompact (closure B)) :
    IsCompact {p : T × E | p.2 ∈ closure (minkowskiDomain p.1 A B)} := by
  let S : Set (T × (E × E)) := univ ×ˢ (closure A ×ˢ closure B)
  let F : T × (E × E) → T × E := fun p =>
    (p.1,(p.1 : ℝ) • p.2.1+(1-(p.1 : ℝ)) • p.2.2)
  have hS : IsCompact S := (isCompact_univ : IsCompact (univ : Set T)).prod (hAK.prod hBK)
  have hF : Continuous F := by fun_prop
  have he : F '' S = {p : T × E | p.2 ∈ closure (minkowskiDomain p.1 A B)} := by
    ext p
    constructor
    · rintro ⟨⟨t,a,b⟩,⟨_,ha,hb⟩,rfl⟩
      change (t : ℝ) • a+(1-(t : ℝ)) • b ∈ closure (minkowskiDomain t A B)
      rw [minkowskiDomain_closure hAK hBK]
      exact ⟨(t : ℝ) • a,⟨a,ha,rfl⟩,(1-(t : ℝ)) • b,⟨b,hb,rfl⟩,rfl⟩
    · intro hp
      change p.2 ∈ closure (minkowskiDomain p.1 A B) at hp
      rw [minkowskiDomain_closure hAK hBK] at hp
      rcases hp with ⟨_,⟨a,ha,rfl⟩,_,⟨b,hb,rfl⟩,he⟩
      exact ⟨(p.1,a,b),⟨mem_univ _,ha,hb⟩,Prod.ext rfl he⟩
  rw [← he]
  exact hS.image hF

theorem minkowskiDomain_parameterGraph_isOpen
    {A B : Set E} (hAo : IsOpen A) (hBo : IsOpen B)
    (hA : Convex ℝ A) (hB : Convex ℝ B) {ρ L : ℝ} (hρ : 0 < ρ) (hL : 0 ≤ L)
    (hballA : closedBall (0 : E) ρ ⊆ A) (hballB : closedBall (0 : E) ρ ⊆ B)
    (hAb : ∀ x ∈ A, ‖x‖ ≤ L) (hBb : ∀ x ∈ B, ‖x‖ ≤ L) :
    IsOpen {p : T × E | p.2 ∈ minkowskiDomain p.1 A B} := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  exact minkowskiDomain_joint_mem_nhds hA hB hρ hL hballA hballB hAb hBb
    (minkowskiDomain_isOpen hAo hBo ⟨0,hballA (mem_closedBall_self hρ.le)⟩ p.1) hp

theorem minkowskiDomain_frontier_parameterGraph_isCompact
    {A B : Set E} (hAo : IsOpen A) (hBo : IsOpen B)
    (hAK : IsCompact (closure A)) (hBK : IsCompact (closure B))
    (hA : Convex ℝ A) (hB : Convex ℝ B) {ρ L : ℝ} (hρ : 0 < ρ) (hL : 0 ≤ L)
    (hballA : closedBall (0 : E) ρ ⊆ A) (hballB : closedBall (0 : E) ρ ⊆ B)
    (hAb : ∀ x ∈ A, ‖x‖ ≤ L) (hBb : ∀ x ∈ B, ‖x‖ ≤ L) :
    IsCompact {p : T × E | p.2 ∈ frontier (minkowskiDomain p.1 A B)} := by
  have hC := minkowskiDomain_closure_parameterGraph_isCompact hAK hBK
  have hO := minkowskiDomain_parameterGraph_isOpen hAo hBo hA hB hρ hL hballA hballB hAb hBb
  have he : {p : T × E | p.2 ∈ frontier (minkowskiDomain p.1 A B)} =
      {p : T × E | p.2 ∈ closure (minkowskiDomain p.1 A B)} ∩
      {p : T × E | p.2 ∈ minkowskiDomain p.1 A B}ᶜ := by
    ext p
    rw [mem_setOf_eq,(minkowskiDomain_isOpen hAo hBo
      ⟨0,hballA (mem_closedBall_self hρ.le)⟩ p.1).frontier_eq]
    rfl
  rw [he]
  exact hC.of_isClosed_subset (hC.isClosed.inter hO.isClosed_compl) inter_subset_left

variable [FiniteDimensional ℝ E] [Nontrivial E]

theorem minkowski_distanceInterior_uniform_geometry
    {A B : Set E} (hAo : IsOpen A) (hBo : IsOpen B)
    (hA : Convex ℝ A) (hB : Convex ℝ B) {ρ L ε : ℝ}
    (hρ : 0 < ρ) (hε : 0 < ε) (hερ : ε < ρ)
    (hballA : closedBall (0 : E) ρ ⊆ A) (hballB : closedBall (0 : E) ρ ⊆ B)
    (hAb : ∀ x ∈ A, ‖x‖ ≤ L) (hBb : ∀ x ∈ B, ‖x‖ ≤ L)
    (t : T) :
    let V := distanceInteriorDomain (minkowskiDomain t A B) ε
    IsOpen V ∧ Convex ℝ V ∧ (0 : E) ∈ V ∧ IsCompact (closure V) ∧
      closure V ⊆ minkowskiDomain t A B := by
  let U := minkowskiDomain t A B
  have hU : IsOpen U := minkowskiDomain_isOpen hAo hBo
    ⟨0,hballA (mem_closedBall_self hρ.le)⟩ t
  have hK : IsCompact (closure U) := minkowskiDomain_isCompact_closure hAb hBb t.2.1 t.2.2
  have hproper : U ≠ univ := by
    intro he
    apply hK.ne_univ
    simp only [he,closure_univ]
  have hball : closedBall (0 : E) ρ ⊆ U := fun z hz =>
    minkowskiDomain_contains_inter t A B ⟨hballA hz,hballB hz⟩
  have h0 : (0 : E) ∈ U := hball (mem_closedBall_self hρ.le)
  have hd : ρ ≤ infDist (0 : E) Uᶜ := by
    apply (le_infDist (nonempty_compl.mpr hproper)).mpr
    intro z hz
    by_contra hh
    exact hz (hball (by simpa only [mem_closedBall,dist_comm] using (lt_of_not_ge hh).le))
  have h0V : (0 : E) ∈ distanceInteriorDomain U ε := by
    refine ⟨h0,?_⟩
    change ε < infDist (0 : E) (frontier U)
    rw [infDist_frontier_eq_compl_of_mem hU hproper h0]
    exact hερ.trans_le hd
  exact ⟨distanceInteriorDomain_isOpen hU ε,
    distanceInteriorDomain_convex hU (minkowskiDomain_convex hA hB t) hproper ε,
    h0V,distanceInteriorDomain_isCompact_closure hK ε,
    fun x hx => (distanceInteriorDomain_closure_subset hU hε hx).1⟩

end PowerConvexity
