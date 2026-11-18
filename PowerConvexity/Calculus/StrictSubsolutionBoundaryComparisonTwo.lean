import PowerConvexity.Calculus.ClassicalComparisonTwo
import PowerConvexity.Calculus.ClassicalDefiningNormalTwo

/-! # A strict subsolution controls values and actual inward boundary derivatives

These estimates apply to any actual classical solution, if it exists. They do
not construct that solution and do not assert a parameter-uniform Hessian bound.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Filter
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem strict_subsolution_le_classicalDirichlet_two
    {U : Set E} (hU : IsOpen U) (hK : IsCompact (closure U))
    (a b : Fin 2 → E) {w u : E → ℝ}
    (hwc : ContinuousOn w (closure U)) (hw : ContDiffOn ℝ 2 w U)
    (huc : ContinuousOn u (closure U)) (hu : ContDiffOn ℝ 2 u U)
    (hwp : ∀ x ∈ U, (complexHessian a b w x).PosDef)
    (hwd : ∀ x ∈ U, (1 : ℂ) < (complexHessian a b w x).det)
    (hud : ∀ x ∈ U, (complexHessian a b u x).det = 1)
    (hb : ∀ x ∈ frontier U, w x = u x) :
    ∀ x ∈ closure U, w x ≤ u x := by
  apply classical_strict_comparison_two hU hK a b hwc huc hw hu hwp
  · intro x hx
    rw [hud x hx]
    exact (Complex.lt_def.mp (hwd x hx)).1
  · intro x hx
    exact (hb x hx).le

theorem strict_subsolution_inward_boundary_derivative_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (a b : Fin 2 → E) {w u : E → ℝ}
    (hw : ContDiff ℝ 2 w) (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U)
    (hwp : ∀ x ∈ U, (complexHessian a b w x).PosDef)
    (hwd : ∀ x ∈ U, (1 : ℂ) < (complexHessian a b w x).det)
    (hud : ∀ x ∈ U, (complexHessian a b u x).det = 1)
    (hb : ∀ x ∈ frontier U, w x = u x)
    {x : E} (hx : x ∈ frontier U) :
    ∀ y ∈ closure U, fderiv ℝ w x (y-x) ≤ J.derivative x (y-x) := by
  have hle := strict_subsolution_le_classicalDirichlet_two hU hK a b
    hw.continuous.continuousOn hw.contDiffOn J.continuous_value hu hwp hwd hud hb
  have hm : IsMinOn (fun z => u z-w z) (closure U) x := by
    intro y hy
    change u x-w x ≤ u y-w y
    rw [← hb x hx,sub_self]
    exact sub_nonneg.mpr (hle y hy)
  have hdu := closureJet_hasFDerivWithinAt hU hconv
    (hu.differentiableOn (by norm_num)) J (frontier_subset_closure hx)
  have hdw : HasFDerivWithinAt w (fderiv ℝ w x) (closure U) x :=
    (hw.contDiffAt.differentiableAt (by norm_num)).hasFDerivAt.hasFDerivWithinAt
  intro y hy
  have hh := hm.localize.hasFDerivWithinAt_nonneg (hdu.sub hdw)
    (sub_mem_posTangentConeAt_of_segment_subset
      (hconv.closure.segment_subset (frontier_subset_closure hx) hy))
  simpa only [ContinuousLinearMap.sub_apply,sub_nonneg] using hh

end PowerConvexity
