import PowerConvexity.Calculus.InteriorLevelTruncation
import PowerConvexity.Calculus.StrictPshDirichlet

/-! # Actual interior truncations with positive power Hessian on their boundary

The normal-kernel Hessian hypothesis is explicit. Connectedness of the
truncation is not asserted by this construction.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

theorem negativeLevelDomain_actual_contDiffAt_closure
    {U : Set E} (hU : IsOpen U) {u : E → ℝ}
    (huc : ContinuousOn u (closure U)) (hb : ∀ x ∈ frontier U, u x = 0)
    {ε : ℝ} (hε : 0 < ε) {n : ℕ∞ω} (hu : ContDiffOn ℝ n u U) :
    ∀ x ∈ closure (negativeLevelDomain U u ε), ContDiffAt ℝ n u x := by
  intro x hx
  exact hu.contDiffAt (hU.mem_nhds ((negativeLevelDomain_closure_subset hU huc hb hε hx).1))

theorem powerHessian_positive_level_collar
    {U : Set E} (hU : IsOpen U) (hK : IsCompact (closure U)) {u : E → ℝ}
    (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U)
    (hneg : ∀ x ∈ U, u x < 0) (hb : ∀ x ∈ frontier U, u x = 0)
    (htan : ∀ x ∈ frontier U, ∀ v : E, v ≠ 0 →
      J.derivative x v = 0 → 0 < J.hessian x v v) :
    ∃ δ > 0, ∀ y ∈ U, -δ < u y → ∀ v : E, v ≠ 0 →
      0 < realHessian (powerTransform u) y v v := by
  apply exists_level_collar_of_boundary_germs hU hK J.continuous_value hneg
  intro x hx
  exact powerHessian_positive_near_boundary_of_tangent_positive hU hu J hneg
    (frontier_subset_closure hx) (hb x hx) (htan x hx)

theorem exists_negative_level_truncation_positive_boundary
    {U : Set E} (hU : IsOpen U) (hK : IsCompact (closure U)) (hne : U.Nonempty)
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U)
    (hneg : ∀ x ∈ U, u x < 0) (hb : ∀ x ∈ frontier U, u x = 0)
    (htan : ∀ x ∈ frontier U, ∀ v : E, v ≠ 0 →
      J.derivative x v = 0 → 0 < J.hessian x v v) :
    ∃ ε > 0, let V := negativeLevelDomain U u ε
      IsOpen V ∧ V.Nonempty ∧ IsCompact (closure V) ∧ closure V ⊆ U ∧
      (∀ x ∈ closure V, u x < 0) ∧
      (∀ x ∈ frontier V, ∀ v : E, v ≠ 0 → 0 < realHessian (powerTransform u) x v v) := by
  obtain ⟨δ,hδ,hcollar⟩ := powerHessian_positive_level_collar hU hK hu J hneg hb htan
  obtain ⟨z,hz⟩ := hne
  let ε := min (δ/2) (-u z/2)
  have hε : 0 < ε := lt_min (by positivity) (by linarith [hneg z hz])
  have heδ : ε < δ := (min_le_left _ _).trans_lt (by linarith)
  have hzε : u z < -ε := by
    have he : ε ≤ -u z/2 := min_le_right _ _
    linarith [hneg z hz]
  have hcl := negativeLevelDomain_closure_subset hU J.continuous_value hb hε
  refine ⟨ε,hε,negativeLevelDomain_isOpen hU J.continuous_value ε,⟨z,hz,hzε⟩,
    negativeLevelDomain_isCompact_closure hK u ε,(fun x hx => (hcl hx).1),?_,?_⟩
  · intro x hx
    have hh := (hcl hx).2
    linarith
  · intro x hx
    obtain ⟨hxU,hux⟩ := negativeLevelDomain_frontier_value hU J.continuous_value hb hε x hx
    exact hcollar x hxU (by rw [hux]; linarith)

end PowerConvexity
