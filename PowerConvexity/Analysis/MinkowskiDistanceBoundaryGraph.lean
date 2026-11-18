import PowerConvexity.Analysis.MinkowskiDistanceMinimum

/-! The frontier graph of the actual distance interiors is compact. -/
set_option autoImplicit false
open Set Metric
open scoped Topology
namespace PowerConvexity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
local notation "I" => Icc (0 : ℝ) 1

theorem minkowski_distanceInterior_frontier_parameterGraph_isCompact
    {A B : Set E} (hAo : IsOpen A) (hBo : IsOpen B)
    (hA : Convex ℝ A) (hB : Convex ℝ B) {ρ L ε : ℝ}
    (hρ : 0 < ρ) (hL : 0 ≤ L) (hε : 0 < ε) (hερ : ε < ρ)
    (hballA : closedBall (0 : E) ρ ⊆ A) (hballB : closedBall (0 : E) ρ ⊆ B)
    (hAb : ∀ x ∈ A, ‖x‖ ≤ L) (hBb : ∀ x ∈ B, ‖x‖ ≤ L) :
    IsCompact {p : I × E |
      p.2 ∈ frontier (distanceInteriorDomain (minkowskiDomain p.1 A B) ε)} := by
  have hg := minkowski_distanceInterior_parameterGraphs hAo hBo hA hB hρ hL hε hερ
    hballA hballB hAb hBb
  have he : {p : I × E | p.2 ∈ frontier (distanceInteriorDomain (minkowskiDomain p.1 A B) ε)} =
      {p : I × E | p.2 ∈ closure (distanceInteriorDomain (minkowskiDomain p.1 A B) ε)} ∩
      {p : I × E | p.2 ∈ distanceInteriorDomain (minkowskiDomain p.1 A B) ε}ᶜ := by
    ext p
    rw [mem_setOf_eq, (distanceInteriorDomain_isOpen
      (minkowskiDomain_isOpen hAo hBo ⟨0,hballA (mem_closedBall_self hρ.le)⟩ p.1) ε).frontier_eq]
    rfl
  rw [he]
  exact hg.2.of_isClosed_subset (hg.2.isClosed.inter hg.1.isClosed_compl) inter_subset_left

end PowerConvexity
