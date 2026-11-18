import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! # Actual differentiation of an integral over a compact parameter space.
The dominating derivative bound is constructed on a compact product around
the actual evaluation point. It is not an additional estimate assumption.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology
namespace PowerConvexity
variable {H A F : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [ProperSpace H]
  [TopologicalSpace A] [CompactSpace A] [MeasurableSpace A] [BorelSpace A] [T2Space A] [SecondCountableTopology A]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem compact_parameter_integral_hasFDerivAt
    {μ : Measure A} [IsFiniteMeasure μ] {U : Set H} (hU : IsOpen U)
    {f : H → A → F} {df : H → A → H →L[ℝ] F}
    (hf : ContinuousOn (fun p : H × A => f p.1 p.2) (U ×ˢ univ))
    (hdf : ContinuousOn (fun p : H × A => df p.1 p.2) (U ×ˢ univ))
    (hderiv : ∀ x ∈ U, ∀ a, HasFDerivAt (fun y => f y a) (df x a) x)
    {x : H} (hx : x ∈ U) :
    HasFDerivAt (fun y => ∫ a, f y a ∂μ) (∫ a, df x a ∂μ) x := by
  have hfc (y : H) (hy : y ∈ U) : Continuous (f y) := by
    exact continuousOn_univ.mp (hf.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun a _ => ⟨hy,mem_univ a⟩))
  have hdc (y : H) (hy : y ∈ U) : Continuous (df y) := by
    exact continuousOn_univ.mp (hdf.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun a _ => ⟨hy,mem_univ a⟩))
  obtain ⟨r,hr,hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  have hr2 : 0 < r/2 := half_pos hr
  have hK : closedBall x (r/2) ⊆ U := by
    intro y hy
    exact hrU (mem_ball.mpr ((mem_closedBall.mp hy).trans_lt (by linarith)))
  obtain ⟨M,hM⟩ := ((isCompact_closedBall x (r/2)).prod (isCompact_univ : IsCompact (univ : Set A))).exists_bound_of_continuousOn
    (hdf.mono (by intro p hp; exact ⟨hK hp.1,hp.2⟩))
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F' := df) (bound := fun _ => M) (closedBall_mem_nhds x hr2)
  · filter_upwards [hU.mem_nhds hx] with y hy
    exact (hfc y hy).aestronglyMeasurable
  · exact (hfc x hx).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · exact (hdc x hx).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun a y hy => hM (y,a) ⟨hy,mem_univ a⟩)
  · exact integrable_const M
  · exact Filter.Eventually.of_forall (fun a y hy => hderiv y (hK hy) a)

theorem compact_parameter_integral_C1
    {μ : Measure A} [IsFiniteMeasure μ] {U : Set H} (hU : IsOpen U)
    {f : H → A → F} {df : H → A → H →L[ℝ] F}
    (hf : ContinuousOn (fun p : H × A => f p.1 p.2) (U ×ˢ univ))
    (hdf : ContinuousOn (fun p : H × A => df p.1 p.2) (U ×ˢ univ))
    (hderiv : ∀ x ∈ U, ∀ a, HasFDerivAt (fun y => f y a) (df x a) x) :
    ContDiffOn ℝ 1 (fun y => ∫ a, f y a ∂μ) U := by
  have hc : ContinuousOn (fun y => ∫ a, df y a ∂μ) U :=
    continuousOn_integral_of_compact_support isCompact_univ hdf
      (by intro p a hp ha; exact (ha (mem_univ a)).elim)
  intro x hx
  apply ContDiffAt.contDiffWithinAt
  change ContDiffAt ℝ ((0 : ℕ)+1) (fun y => ∫ a, f y a ∂μ) x
  apply contDiffAt_succ_iff_hasFDerivAt.mpr
  refine ⟨fun y => ∫ a, df y a ∂μ,⟨U,hU.mem_nhds hx,?_⟩,?_⟩
  · intro y hy
    exact compact_parameter_integral_hasFDerivAt hU hf hdf hderiv hy
  · exact contDiffAt_zero.mpr ⟨U,hU.mem_nhds hx,hc⟩

theorem compact_parameter_integral_C2
    {μ : Measure A} [IsFiniteMeasure μ] {U : Set H} (hU : IsOpen U)
    {f : H → A → F} {df : H → A → H →L[ℝ] F}
    {ddf : H → A → H →L[ℝ] H →L[ℝ] F}
    (hf : ContinuousOn (fun p : H × A => f p.1 p.2) (U ×ˢ univ))
    (hdf : ContinuousOn (fun p : H × A => df p.1 p.2) (U ×ˢ univ))
    (hddf : ContinuousOn (fun p : H × A => ddf p.1 p.2) (U ×ˢ univ))
    (hderiv : ∀ x ∈ U, ∀ a, HasFDerivAt (fun y => f y a) (df x a) x)
    (hderiv2 : ∀ x ∈ U, ∀ a, HasFDerivAt (fun y => df y a) (ddf x a) x) :
    ContDiffOn ℝ 2 (fun y => ∫ a, f y a ∂μ) U := by
  have hc := compact_parameter_integral_C1 (μ := μ) hU hdf hddf hderiv2
  intro x hx
  apply ContDiffAt.contDiffWithinAt
  change ContDiffAt ℝ ((1 : ℕ)+1) (fun y => ∫ a, f y a ∂μ) x
  apply contDiffAt_succ_iff_hasFDerivAt.mpr
  refine ⟨fun y => ∫ a, df y a ∂μ,⟨U,hU.mem_nhds hx,?_⟩,?_⟩
  · intro y hy
    exact compact_parameter_integral_hasFDerivAt hU hf hdf hderiv hy
  · exact hc.contDiffAt (hU.mem_nhds hx)

end PowerConvexity
