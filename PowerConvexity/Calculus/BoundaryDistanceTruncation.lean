import PowerConvexity.Calculus.ConvexDistanceInterior
import PowerConvexity.Analysis.CompactDistanceCollar
import PowerConvexity.Calculus.BoundaryPowerHessian

/-! # The exact frozen interior domain with its geometric and jet properties

Tangent Hessian positivity on the original boundary remains explicit. Given
that input, this file constructs the actual distance truncation used in Section 4.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]

theorem distanceInteriorDomain_actual_contDiffAt_closure
    {U : Set E} (hU : IsOpen U) {u : E → ℝ} {ε : ℝ} (hε : 0 < ε)
    {n : ℕ∞ω} (hu : ContDiffOn ℝ n u U) :
    ∀ x ∈ closure (distanceInteriorDomain U ε), ContDiffAt ℝ n u x := by
  intro x hx
  exact hu.contDiffAt (hU.mem_nhds ((distanceInteriorDomain_closure_subset hU hε hx).1))

theorem exists_distance_truncation_positive_boundary
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U)
    (hK : IsCompact (closure U)) (hne : U.Nonempty)
    {u : E → ℝ} (hu : ContDiffOn ℝ 4 u U) (J : ClosureC2Jet u U)
    (hneg : ∀ x ∈ U, u x < 0) (hb : ∀ x ∈ frontier U, u x = 0)
    (htan : ∀ x ∈ frontier U, ∀ v : E, v ≠ 0 →
      J.derivative x v = 0 → 0 < J.hessian x v v) :
    ∃ ε > 0, let V := distanceInteriorDomain U ε
      IsOpen V ∧ Convex ℝ V ∧ V.Nonempty ∧ IsCompact (closure V) ∧ closure V ⊆ U ∧
      (∀ x ∈ closure V, ContDiffAt ℝ 4 u x) ∧ (∀ x ∈ closure V, u x < 0) ∧
      (∀ x ∈ frontier V, ∀ v : E, v ≠ 0 → 0 < realHessian (powerTransform u) x v v) := by
  have hproper : U ≠ univ := by
    intro he
    apply hK.ne_univ
    simp only [he,closure_univ]
  obtain ⟨z,hz⟩ := hne
  obtain ⟨w,hw,_⟩ := exists_mem_frontier_infDist_compl_eq_dist hz hproper
  have hF : (frontier U).Nonempty := ⟨w,hw⟩
  obtain ⟨δ,hδ,hcollar⟩ := exists_distance_collar_of_boundary_germs hK hF
    (P := fun x => ∀ v : E, v ≠ 0 → 0 < realHessian (powerTransform u) x v v)
    (fun x hx => powerHessian_positive_near_boundary_of_tangent_positive hU
      (hu.of_le (by norm_num)) J hneg (frontier_subset_closure hx) (hb x hx) (htan x hx))
  obtain ⟨r,hr,hrV⟩ := exists_distanceInteriorDomain_nonempty_radius hU hproper ⟨z,hz⟩
  let ε := min (δ/2) r
  have hε : 0 < ε := lt_min (by positivity) hr
  have heδ : ε < δ := (min_le_left _ _).trans_lt (by linarith)
  have hcl : closure (distanceInteriorDomain U ε) ⊆ U :=
    fun x hx => (distanceInteriorDomain_closure_subset hU hε hx).1
  refine ⟨ε,hε,distanceInteriorDomain_isOpen hU ε,
    distanceInteriorDomain_convex hU hconv hproper ε,hrV ε (min_le_right _ _),
    distanceInteriorDomain_isCompact_closure hK ε,hcl,
    distanceInteriorDomain_actual_contDiffAt_closure hU hε hu,
    (fun x hx => hneg x (hcl hx)),?_⟩
  intro x hx
  obtain ⟨hxU,hxd⟩ := distanceInteriorDomain_frontier_value hU hε x hx
  exact hcollar x hxU (by rw [hxd]; exact heδ)

end PowerConvexity
