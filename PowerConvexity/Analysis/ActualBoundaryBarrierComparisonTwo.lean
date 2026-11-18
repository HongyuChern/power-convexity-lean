import PowerConvexity.Analysis.ActualPositiveBoundaryBarrierH01Two
import PowerConvexity.Analysis.ActualZeroTraceComparisonTwo

/-! # Actual boundary continuity from a genuine zero-trace barrier

Comparison is performed in the original H01 test space. The pointwise zero
extension is then proved continuous, including every actual boundary point.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)

theorem actual_zero_extension_continuous_of_barrier_two
    {U : Set E} (hU : IsOpen U) {u p : E → ℝ}
    (hu : ContinuousOn u U) (hp : Continuous p)
    (hp0 : ∀ x ∈ frontier U, p x = 0)
    (hbound : ∀ x ∈ U, |u x| ≤ p x) : Continuous (U.indicator u) := by
  classical
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ U
  · apply (hu.continuousAt (hU.mem_nhds hx)).congr
    filter_upwards [hU.mem_nhds hx] with y hy
    exact (Set.indicator_of_mem hy u).symm
  · by_cases hxK : x ∈ closure U
    · have hxf : x ∈ frontier U := by
        rw [hU.frontier_eq]
        exact ⟨hxK,hx⟩
      have hplim : Tendsto (fun y => ‖p y‖) (𝓝 x) (𝓝 0) := by
        have hpc : ContinuousAt p x := hp.continuousAt
        simpa only [hp0 x hxf,norm_zero] using hpc.norm.tendsto
      have hb : ∀ y, ‖U.indicator u y‖ ≤ ‖p y‖ := by
        intro y
        by_cases hy : y ∈ U
        · rw [Set.indicator_of_mem hy,Real.norm_eq_abs,Real.norm_eq_abs]
          exact (hbound y hy).trans (le_abs_self _)
        · rw [Set.indicator_of_notMem hy,norm_zero]
          exact norm_nonneg _
      change Tendsto (U.indicator u) (𝓝 x) (𝓝 (U.indicator u x))
      rw [Set.indicator_of_notMem hx]
      exact squeeze_zero_norm hb hplim
    · apply continuousAt_const.congr
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hxK] with y hy
      exact (Set.indicator_of_notMem (fun h => hy (subset_closure h)) u).symm

theorem actual_zeroTrace_scalar_barrier_abs_two
    {U : Set E} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {A : EllipticCoeff (2+2) U} {f g u p : E → ℝ}
    (hf : MemLp f 2 (volume.restrict U)) (hg : MemLp g 2 (volume.restrict U))
    (hu : ActualScalarWeakEquationTwo A f u) (hp : ActualScalarWeakEquationTwo A g p)
    (hu0 : MemH01 u U) (hp0 : MemH01 p U)
    (huC : ContinuousOn u U) (hpC : ContinuousOn p U)
    (hfg : ∀ᵐ x ∂volume.restrict U, |f x| ≤ g x) :
    ∀ x ∈ U, |u x| ≤ p x := by
  have hup : ∀ x ∈ U, u x ≤ p x :=
    actual_continuous_zeroTrace_scalar_comparison_two hU hUb hf hg hu hp
      (MemW01p.sub hu0 hp0)
      (hfg.mono (fun x hx => (le_abs_self _).trans hx)) huC hpC
  have hneg := actual_scalar_weak_smul_two hU hu (-1)
  have hnup : ∀ x ∈ U, (-1)*u x ≤ p x :=
    actual_continuous_zeroTrace_scalar_comparison_two hU hUb (hf.const_mul (-1)) hg hneg hp
      (MemW01p.sub (MemW01p.smul (-1) hu0) hp0)
      (hfg.mono (fun x hx => by simpa only [neg_one_mul] using (neg_le_abs _).trans hx))
      (continuousOn_const.mul huC) hpC
  intro x hx
  exact abs_le.mpr ⟨by have hh := hnup x hx; nlinarith,hup x hx⟩

theorem actual_zeroTrace_C2_zero_boundary_of_barrier_two
    {U : Set E} (hU : IsOpen U) (hK : IsCompact (closure U))
    {A : EllipticCoeff (2+2) U} {f g u p : E → ℝ}
    (hf : MemLp f 2 (volume.restrict U)) (hg : MemLp g 2 (volume.restrict U))
    (hu : ActualScalarWeakEquationTwo A f u) (hpw : ActualScalarWeakEquationTwo A g p)
    (hu0 : MemH01 u U) (huC : ContDiffOn ℝ 2 u U)
    (hpC : ContDiff ℝ 1 p) (hpos : ∀ x ∈ U, 0 < p x)
    (hp0 : ∀ x ∈ frontier U, p x = 0)
    (hfg : ∀ᵐ x ∂volume.restrict U, |f x| ≤ g x) :
    ∃ v : E → ℝ, EqOn v u U ∧ v =ᵐ[volume.restrict U] u ∧
      Continuous v ∧ ContDiffOn ℝ 2 v U ∧ MemH01 v U ∧
      ActualScalarWeakEquationTwo A f v ∧ (∀ x ∉ U, v x = 0) := by
  classical
  have hpz := actual_positive_boundary_barrier_memH01_two hU hK hpC hpos hp0
  have hbound := actual_zeroTrace_scalar_barrier_abs_two hU
    (hK.isBounded.subset subset_closure) hf hg hu hpw hu0 hpz huC.continuousOn hpC.continuous.continuousOn hfg
  let v : E → ℝ := U.indicator u
  have he : EqOn v u U := fun x hx => Set.indicator_of_mem hx _
  have hae : v =ᵐ[volume.restrict U] u := by
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    exact he hx
  have hvC : ContDiffOn ℝ 2 v U := by
    intro x hx
    apply ((huC.contDiffAt (hU.mem_nhds hx)).congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [hU.mem_nhds hx] with y hy
    exact he hy
  refine ⟨v,he,hae,actual_zero_extension_continuous_of_barrier_two hU huC.continuousOn
    hpC.continuous hp0 hbound,hvC,actual_zeroTrace_congr_ae hae.symm hu0,
    actual_scalar_weak_congr_ae_two hae.symm hu,?_⟩
  intro x hx
  exact Set.indicator_of_notMem hx _

end PowerConvexity
