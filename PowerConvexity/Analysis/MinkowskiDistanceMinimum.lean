import PowerConvexity.Analysis.DistanceInteriorBallCenters
import PowerConvexity.Analysis.MinkowskiParameterGeometry
import PowerConvexity.Analysis.MinimumOnVaryingDomain

/-! # Minimum continuity on the actual distance-truncated Minkowski domains

The open graph is obtained by compact quantification over a fixed closed
epsilon-ball. The closure graph is compact by the closed-ball center
description. Consequently no unconstructed family of homeomorphisms is
needed to prove continuity of a jointly continuous spectral minimum.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric Filter
open scoped Topology
namespace PowerConvexity
variable {T E : Type*} [TopologicalSpace T]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem ballCenterSet_parameterGraph_isOpen [ProperSpace E]
    {U : T → Set E} (hU : IsOpen {p : T × E | p.2 ∈ U p.1}) (ε : ℝ) :
    IsOpen {p : T × E | p.2 ∈ ballCenterSet (U p.1) ε} := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  change ∀ᶠ q in 𝓝 p, ∀ z ∈ closedBall (0 : E) ε, q.2+z ∈ U q.1
  apply (isCompact_closedBall (0 : E) ε).eventually_forall_of_forall_eventually
  intro z hz
  have hc : Continuous (fun q : (T × E) × E => (q.1.1,q.1.2+q.2)) := by fun_prop
  exact (hc.continuousAt (x := (p,z))).tendsto.eventually
    (hU.mem_nhds (show (p.1,p.2+z) ∈ {q : T × E | q.2 ∈ U q.1} from hp z hz))

theorem ballCenterSet_parameterGraph_isClosed
    {K : T → Set E} (hK : IsClosed {p : T × E | p.2 ∈ K p.1}) (ε : ℝ) :
    IsClosed {p : T × E | p.2 ∈ ballCenterSet (K p.1) ε} := by
  have he : {p : T × E | p.2 ∈ ballCenterSet (K p.1) ε} =
      ⋂ z : closedBall (0 : E) ε,
        (fun p : T × E => (p.1,p.2+(z : E))) ⁻¹' {p : T × E | p.2 ∈ K p.1} := by
    ext p
    simp only [mem_setOf_eq,ballCenterSet,mem_iInter,mem_preimage]
    exact ⟨fun h z => h z z.property,fun h z hz => h ⟨z,hz⟩⟩
  rw [he]
  exact isClosed_iInter (fun z => hK.preimage (by fun_prop))

theorem ballCenterSet_parameterGraph_isCompact [T2Space T]
    {K : T → Set E} (hK : IsCompact {p : T × E | p.2 ∈ K p.1})
    {ε : ℝ} (hε : 0 ≤ ε) :
    IsCompact {p : T × E | p.2 ∈ ballCenterSet (K p.1) ε} := by
  apply hK.of_isClosed_subset (ballCenterSet_parameterGraph_isClosed hK.isClosed ε)
  intro p hp
  change p.2 ∈ K p.1
  simpa only [add_zero] using hp 0 (mem_closedBall_self hε)

variable [FiniteDimensional ℝ E] [Nontrivial E]
local notation "I" => Icc (0 : ℝ) 1

theorem minkowski_distanceInterior_parameterGraphs
    {A B : Set E} (hAo : IsOpen A) (hBo : IsOpen B)
    (hA : Convex ℝ A) (hB : Convex ℝ B) {ρ L ε : ℝ}
    (hρ : 0 < ρ) (hL : 0 ≤ L) (hε : 0 < ε) (hερ : ε < ρ)
    (hballA : closedBall (0 : E) ρ ⊆ A) (hballB : closedBall (0 : E) ρ ⊆ B)
    (hAb : ∀ x ∈ A, ‖x‖ ≤ L) (hBb : ∀ x ∈ B, ‖x‖ ≤ L) :
    IsOpen {p : I × E | p.2 ∈ distanceInteriorDomain (minkowskiDomain p.1 A B) ε} ∧
    IsCompact {p : I × E | p.2 ∈ closure (distanceInteriorDomain (minkowskiDomain p.1 A B) ε)} := by
  have hV (t : I) : IsOpen (minkowskiDomain t A B) :=
    minkowskiDomain_isOpen hAo hBo ⟨0,hballA (mem_closedBall_self hρ.le)⟩ t
  have hK (t : I) : IsCompact (closure (minkowskiDomain t A B)) :=
    minkowskiDomain_isCompact_closure hAb hBb t.2.1 t.2.2
  have hp (t : I) : minkowskiDomain t A B ≠ univ := by
    intro he
    apply (hK t).ne_univ
    simp only [he,closure_univ]
  have hb (t : I) : closedBall (0 : E) ρ ⊆ minkowskiDomain t A B :=
    fun z hz => minkowskiDomain_contains_inter t A B ⟨hballA hz,hballB hz⟩
  have hAK : IsCompact (closure A) :=
    (isBounded_iff_forall_norm_le.mpr ⟨L,hAb⟩).isCompact_closure
  have hBK : IsCompact (closure B) :=
    (isBounded_iff_forall_norm_le.mpr ⟨L,hBb⟩).isCompact_closure
  constructor
  · have he : {p : I × E | p.2 ∈ distanceInteriorDomain (minkowskiDomain p.1 A B) ε} =
        {p : I × E | p.2 ∈ ballCenterSet (minkowskiDomain p.1 A B) ε} := by
      ext p
      simp only [mem_setOf_eq]
      rw [distanceInteriorDomain_eq_ballCenterSet (hV p.1) (hp p.1) hε.le]
    rw [he]
    exact ballCenterSet_parameterGraph_isOpen (U := fun t : I => minkowskiDomain t A B)
      (minkowskiDomain_parameterGraph_isOpen hAo hBo hA hB hρ hL hballA hballB hAb hBb) ε
  · have he : {p : I × E | p.2 ∈ closure (distanceInteriorDomain (minkowskiDomain p.1 A B) ε)} =
        {p : I × E | p.2 ∈ ballCenterSet (closure (minkowskiDomain p.1 A B)) ε} := by
      ext p
      simp only [mem_setOf_eq]
      rw [distanceInteriorDomain_closure_eq_ballCenterSet (hV p.1)
        (minkowskiDomain_convex hA hB p.1) (hp p.1) hε.le hερ (hb p.1)]
    rw [he]
    exact ballCenterSet_parameterGraph_isCompact (K := fun t : I => closure (minkowskiDomain t A B))
      (minkowskiDomain_closure_parameterGraph_isCompact hAK hBK) hε.le

theorem minkowski_distanceInterior_minimum_continuous
    {A B : Set E} (hAo : IsOpen A) (hBo : IsOpen B)
    (hA : Convex ℝ A) (hB : Convex ℝ B) {ρ L ε : ℝ}
    (hρ : 0 < ρ) (hL : 0 ≤ L) (hε : 0 < ε) (hερ : ε < ρ)
    (hballA : closedBall (0 : E) ρ ⊆ A) (hballB : closedBall (0 : E) ρ ⊆ B)
    (hAb : ∀ x ∈ A, ‖x‖ ≤ L) (hBb : ∀ x ∈ B, ‖x‖ ≤ L)
    {F : I × E → ℝ}
    (hF : ContinuousOn F {p : I × E |
      p.2 ∈ closure (distanceInteriorDomain (minkowskiDomain p.1 A B) ε)}) :
    Continuous (fun t : I => sInf ((fun x => F (t,x)) ''
      closure (distanceInteriorDomain (minkowskiDomain t A B) ε))) := by
  have hg := minkowski_distanceInterior_parameterGraphs hAo hBo hA hB hρ hL hε hερ
    hballA hballB hAb hBb
  have hv (t : I) := minkowski_distanceInterior_uniform_geometry hAo hBo hA hB hρ hε hερ
    hballA hballB hAb hBb t
  exact continuous_minimum_of_open_graph_compact_closure_graph hg.1 hg.2
    (fun t => (hv t).2.2.2.1) (fun t => ⟨0,(hv t).2.2.1⟩) hF

end PowerConvexity
