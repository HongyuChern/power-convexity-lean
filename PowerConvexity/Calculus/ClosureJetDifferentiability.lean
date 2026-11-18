import CHS.Calculus.ClosureRegularity
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! # Actual one-sided derivatives of the prescribed closure jet

On an open convex domain a continuous extension of the interior derivative
is the derivative within the closure. The same assertion is proved for the
first derivative field and its Hessian extension. No ambient extension of
the potential across the boundary is assumed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem closureJet_hasFDerivWithinAt
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U)
    {u : E → ℝ} (hu : DifferentiableOn ℝ u U) (J : ClosureC2Jet u U)
    {x : E} (hx : x ∈ closure U) :
    HasFDerivWithinAt u (J.derivative x) (closure U) x := by
  apply hasFDerivWithinAt_closure_of_tendsto_fderiv hu hconv hU
    (fun y hy => (J.continuous_value y hy).mono subset_closure)
  have h := (J.continuous_derivative x hx).mono subset_closure
  apply h.tendsto.congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact J.derivative_eq hy

theorem closureJet_derivative_hasFDerivAt_interior
    {U : Set E} (hU : IsOpen U) {u : E → ℝ}
    (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U)
    {x : E} (hx : x ∈ U) :
    HasFDerivAt J.derivative (J.hessian x) x := by
  have hux := hu.contDiffAt (hU.mem_nhds hx)
  have hd := ((hux.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasFDerivAt
  rw [← J.hessian_eq hx] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [hU.mem_nhds hx] with y hy
  exact J.derivative_eq hy

theorem closureJet_derivative_hasFDerivWithinAt
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U)
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U)
    {x : E} (hx : x ∈ closure U) :
    HasFDerivWithinAt J.derivative (J.hessian x) (closure U) x := by
  have hd (y : E) (hy : y ∈ U) := closureJet_derivative_hasFDerivAt_interior hU hu J hy
  apply hasFDerivWithinAt_closure_of_tendsto_fderiv
    (fun y hy => (hd y hy).differentiableAt.differentiableWithinAt) hconv hU
    (fun y hy => (J.continuous_derivative y hy).mono subset_closure)
  have h := (J.continuous_hessian x hx).mono subset_closure
  apply h.tendsto.congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact (hd y hy).fderiv.symm

theorem closureJet_hessian_symmetric
    {U : Set E} (hU : IsOpen U) {u : E → ℝ}
    (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U)
    {x : E} (hx : x ∈ closure U) (v w : E) :
    J.hessian x v w = J.hessian x w v := by
  have he : EqOn (fun y => J.hessian y v w) (fun y => J.hessian y w v) U := by
    intro y hy
    change J.hessian y v w = J.hessian y w v
    rw [J.hessian_eq hy]
    exact (hu.contDiffAt (hU.mem_nhds hy)).isSymmSndFDerivAt (by norm_num) v w
  have hc₁ : ContinuousOn (fun y => J.hessian y v w) (closure U) :=
    (J.continuous_hessian.clm_apply continuousOn_const).clm_apply continuousOn_const
  have hc₂ : ContinuousOn (fun y => J.hessian y w v) (closure U) :=
    (J.continuous_hessian.clm_apply continuousOn_const).clm_apply continuousOn_const
  exact he.of_subset_closure hc₁ hc₂ subset_closure Subset.rfl hx

end PowerConvexity
