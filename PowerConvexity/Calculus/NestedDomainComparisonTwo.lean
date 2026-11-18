import PowerConvexity.Calculus.ClassicalC0StabilityTwo
import Mathlib.Topology.Algebra.Indicator

/-! # Domain monotonicity for actual zero-boundary classical solutions -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem dirichlet_zeroExtension_continuous {U : Set E} {u : E → ℝ}
    (huc : ContinuousOn u (closure U)) (hb : ∀ x ∈ frontier U, u x = 0) :
    Continuous (U.indicator u) := continuous_indicator hb huc

theorem strictPshDirichlet_zeroExtension_nonpos {U : Set E}
    (hU : IsOpen U) (hK : IsCompact (closure U))
    {u : E → ℝ} (huc : ContinuousOn u (closure U)) (hu : ContDiffOn ℝ 2 u U)
    (hb : ∀ x ∈ frontier U, u x = 0)
    (a b : Fin 2 → E) (hpsh : ∀ x ∈ U, (complexHessian a b u x).PosDef) :
    ∀ x, U.indicator u x ≤ 0 := by
  classical
  intro x
  by_cases hx : x ∈ U
  · rw [Set.indicator_of_mem hx]
    exact (strictPshDirichlet_negative hU hK huc hu hb a b hpsh x hx).le
  · rw [Set.indicator_of_notMem hx]

theorem nested_dirichlet_zeroExtensions_le_two {U V : Set E}
    (hU : IsOpen U) (hV : IsOpen V) (hKU : IsCompact (closure U))
    (hKV : IsCompact (closure V)) (hUV : U ⊆ V)
    (a b : Fin 2 → E) (hab : Orthonormal ℝ (Sum.elim a b))
    {u v : E → ℝ}
    (huc : ContinuousOn u (closure U)) (hvc : ContinuousOn v (closure V))
    (hu : ContDiffOn ℝ 2 u U) (hv : ContDiffOn ℝ 2 v V)
    (hAv : ∀ x ∈ V, (complexHessian a b v x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian a b u x).det = (complexHessian a b v x).det)
    (hbu : ∀ x ∈ frontier U, u x = 0) (hbv : ∀ x ∈ frontier V, v x = 0) :
    ∀ x, V.indicator v x ≤ U.indicator u x := by
  classical
  have hnonpos : ∀ x ∈ closure V, v x ≤ 0 := by
    intro x hx
    by_cases hi : x ∈ V
    · exact (strictPshDirichlet_negative hV hKV hvc hv hbv a b hAv x hi).le
    · rw [hbv x (by rw [hV.frontier_eq]; exact ⟨hx,hi⟩)]
  have hc : ∀ x ∈ closure U, v x ≤ u x := by
    apply classical_comparison_two hU hKU a b hab (hvc.mono (closure_mono hUV)) huc
      (hv.mono hUV) hu (fun x hx => hAv x (hUV hx))
      (fun x hx => le_of_eq (congrArg Complex.re (hdet x hx)))
    intro x hx
    rw [hbu x hx]
    exact hnonpos x (closure_mono hUV (frontier_subset_closure hx))
  intro x
  by_cases hxU : x ∈ U
  · rw [Set.indicator_of_mem hxU,Set.indicator_of_mem (hUV hxU)]
    exact hc x (subset_closure hxU)
  · rw [Set.indicator_of_notMem hxU]
    by_cases hxV : x ∈ V
    · rw [Set.indicator_of_mem hxV]
      exact hnonpos x (subset_closure hxV)
    · rw [Set.indicator_of_notMem hxV]

end PowerConvexity
