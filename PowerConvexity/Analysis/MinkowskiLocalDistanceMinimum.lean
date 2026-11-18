import PowerConvexity.Analysis.MinkowskiDistanceMinimum
import PowerConvexity.Analysis.LocalMinimumOnVaryingDomain

/-! # Positive-parameter continuity of minima on actual distance truncations -/
set_option autoImplicit false
open Set Metric Filter
open scoped Topology
namespace PowerConvexity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
local notation "I" => Icc (0 : ℝ) 1

theorem minkowski_distanceInterior_minimum_continuousAt_of_pos
    {A B : Set E} (hAo : IsOpen A) (hBo : IsOpen B)
    (hA : Convex ℝ A) (hB : Convex ℝ B) {rho L eps : ℝ}
    (hrho : 0 < rho) (hL : 0 ≤ L) (heps : 0 < eps) (hepsrho : eps < rho)
    (hballA : closedBall (0 : E) rho ⊆ A) (hballB : closedBall (0 : E) rho ⊆ B)
    (hAb : ∀ x ∈ A, ‖x‖ ≤ L) (hBb : ∀ x ∈ B, ‖x‖ ≤ L)
    {F : I × E → ℝ}
    (hF : ContinuousOn F {p : I × E | 0 < (p.1 : ℝ) ∧
      p.2 ∈ closure (distanceInteriorDomain (minkowskiDomain p.1 A B) eps)})
    {s : I} (hs : 0 < (s : ℝ)) :
    ContinuousAt (fun t : I => sInf ((fun x => F (t,x)) ''
      closure (distanceInteriorDomain (minkowskiDomain t A B) eps))) s := by
  let N : Set I := {t | (s : ℝ)/2 ≤ (t : ℝ)}
  have hN : IsClosed N := isClosed_le continuous_const continuous_subtype_val
  have hsN : N ∈ 𝓝 s := continuous_subtype_val.continuousAt.tendsto.eventually
    (Ici_mem_nhds (by linarith : (s : ℝ)/2 < (s : ℝ)))
  have hg := minkowski_distanceInterior_parameterGraphs hAo hBo hA hB hrho hL heps hepsrho
    hballA hballB hAb hBb
  have hv (t : I) := minkowski_distanceInterior_uniform_geometry hAo hBo hA hB hrho heps hepsrho
    hballA hballB hAb hBb t
  apply continuousAt_minimum_of_joint_continuity_on_closed_neighborhood hg.1 hg.2
    (fun t => (hv t).2.2.2.1) (fun t => ⟨0,(hv t).2.2.1⟩) hN hsN
  apply hF.mono
  intro p hp
  exact ⟨(half_pos hs).trans_le hp.1,hp.2⟩

end PowerConvexity
