import PowerConvexity.Calculus.QuadraticTaylor
import PowerConvexity.Calculus.QuadraticL2Control
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Nondegeneracy of the actual L2 energy on quadratic functions

A nonempty interior and a measure positive on nonempty open sets are explicit.
Compactness alone would not imply this conclusion.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped Topology
namespace PowerConvexity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem quadraticL2Energy_eq_zero_iff (μ : Measure E)
    [IsFiniteMeasureOnCompacts μ] [Measure.IsOpenPosMeasure μ]
    {K : Set E} (hK : IsCompact K) (hKi : (interior K).Nonempty)
    {q : E → ℝ} (hq : IsQuadraticPolynomial q) :
    quadraticL2Energy μ K q = 0 ↔ q = 0 := by
  constructor
  · intro he
    have hc : Continuous q := (IsQuadraticPolynomial_contDiff hq 0).continuous
    have hqi : IntegrableOn (fun y => (q y)^2) K μ :=
      (hc.pow 2).continuousOn.integrableOn_compact hK
    have hs : (fun y => (q y)^2) =ᵐ[μ.restrict K] 0 :=
      (setIntegral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall fun y => sq_nonneg (q y)) hqi).mp he
    have hz : q =ᵐ[μ.restrict K] 0 := hs.mono fun y hy => sq_eq_zero_iff.mp hy
    have hzI : EqOn q 0 (interior K) := Measure.eqOn_open_of_ae_eq
      (ae_restrict_of_ae_restrict_of_subset interior_subset hz) isOpen_interior
      hc.continuousOn continuousOn_const
    obtain ⟨x,hx⟩ := hKi
    apply quadratic_zero_of_eventually_zero hq (x := x)
    filter_upwards [isOpen_interior.mem_nhds hx] with y hy
    exact hzI hy
  · rintro rfl
    simp [quadraticL2Energy]

theorem quadraticL2Energy_pos_of_ne_zero (μ : Measure E)
    [IsFiniteMeasureOnCompacts μ] [Measure.IsOpenPosMeasure μ]
    {K : Set E} (hK : IsCompact K) (hKi : (interior K).Nonempty)
    {q : E → ℝ} (hq : IsQuadraticPolynomial q) (hq0 : q ≠ 0) :
    0 < quadraticL2Energy μ K q := by
  exact lt_of_le_of_ne (quadraticL2Energy_nonneg μ K q)
    (Ne.symm fun h => hq0 ((quadraticL2Energy_eq_zero_iff μ hK hKi hq).mp h))

end PowerConvexity
