import PowerConvexity.Analysis.ActualBoundaryVanishingTruncationTwo
import PowerConvexity.Analysis.ActualDominatedL2ConvergenceTwo

/-! # A genuine positive smooth boundary barrier belongs to H01

The zero-trace conclusion is obtained by compactly supported truncation and
strong Sobolev convergence on the original domain.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology ENNReal
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)

def actualClassicalBoundedWitnessTwo {U : Set E}
    (hU : IsOpen U) (hK : IsCompact (closure U)) {p : E → ℝ}
    (hp : ContDiff ℝ 1 p) : MemW1pWitness 2 p U where
  memLp := continuousOn_memLp_two_of_subset_compact hU.measurableSet hK
    subset_closure hp.continuous.continuousOn
  weakGrad := smoothGradField p
  weakGrad_component_memLp := by
    intro i
    exact continuousOn_memLp_two_of_subset_compact hU.measurableSet hK
      subset_closure (((hp.continuous_fderiv one_ne_zero).clm_apply
        (continuous_const : Continuous (fun _ : E => EuclideanSpace.single i (1 : ℝ))))).continuousOn
  isWeakGrad := by
    intro i
    simpa only [smoothGradField,PiLp.toLp_apply] using
      hasWeakPartialDeriv_of_contDiffOn hU hp.contDiffOn i

theorem actual_boundary_value_truncation_support_two
    {U : Set E} (hU : IsOpen U) {p : E → ℝ} (hp : Continuous p)
    (hp0 : ∀ x ∈ frontier U, p x = 0) (n : ℕ) :
    tsupport (U.indicator (fun x => actualBoundaryValueCutoffTwo n (p x))) ⊆ U := by
  classical
  let φ := U.indicator (fun x => actualBoundaryValueCutoffTwo n (p x))
  have hs : Function.support φ ⊆ closure U ∩ {x | 1 ≤ ((n : ℝ)+1)*p x} := by
    intro x hx
    have hxU : x ∈ U := by
      by_contra hn
      exact hx (Set.indicator_of_notMem hn _)
    refine ⟨subset_closure hxU,?_⟩
    by_contra hn
    have hh := actual_boundary_value_cutoff_zero_two n (le_of_lt (lt_of_not_ge hn))
    exact hx (by simpa only [φ,Set.indicator_of_mem hxU] using hh)
  have hcl : IsClosed (closure U ∩ {x | 1 ≤ ((n : ℝ)+1)*p x}) :=
    isClosed_closure.inter (isClosed_le continuous_const (continuous_const.mul hp))
  have ht : tsupport φ ⊆ closure U ∩ {x | 1 ≤ ((n : ℝ)+1)*p x} := closure_minimal hs hcl
  intro x hx
  have hh := ht hx
  by_contra hn
  have hxf : x ∈ frontier U := by
    rw [hU.frontier_eq]
    exact ⟨hh.1,hn⟩
  have h0 := hp0 x hxf
  have hbad : (1 : ℝ) ≤ 0 := by simpa only [Set.mem_setOf_eq,h0,mul_zero] using hh.2
  linarith

theorem actual_boundary_value_truncation_C1_two
    {U : Set E} (hU : IsOpen U) {p : E → ℝ} (hp : ContDiff ℝ 1 p)
    (hp0 : ∀ x ∈ frontier U, p x = 0) (n : ℕ) :
    ContDiff ℝ 1 (U.indicator (fun x => actualBoundaryValueCutoffTwo n (p x))) := by
  classical
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · apply (((actual_boundary_value_cutoff_contDiff_two n).of_le (by simp)).comp hp).contDiffAt.congr_of_eventuallyEq
    filter_upwards [hU.mem_nhds hx] with y hy
    exact Set.indicator_of_mem hy _
  · have hs := actual_boundary_value_truncation_support_two hU hp.continuous hp0 n
    have hx' : x ∉ tsupport (U.indicator (fun y => actualBoundaryValueCutoffTwo n (p y))) :=
      fun hh => hx (hs hh)
    exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hx')

theorem actual_boundary_value_truncation_fderiv_two
    {U : Set E} (hU : IsOpen U) {p : E → ℝ} (hp : ContDiff ℝ 1 p)
    (n : ℕ) {x : E} (hx : x ∈ U) :
    fderiv ℝ (U.indicator (fun y => actualBoundaryValueCutoffTwo n (p y))) x =
      deriv (actualBoundaryValueCutoffTwo n) (p x) • fderiv ℝ p x := by
  have he : U.indicator (fun y => actualBoundaryValueCutoffTwo n (p y)) =ᶠ[𝓝 x]
      (fun y => actualBoundaryValueCutoffTwo n (p y)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact Set.indicator_of_mem hy _
  rw [he.fderiv_eq]
  exact (((actual_boundary_value_cutoff_contDiff_two n).differentiable (by simp) (p x)).hasDerivAt.comp_hasFDerivAt
    x (hp.differentiable one_ne_zero x).hasFDerivAt).fderiv

end PowerConvexity
