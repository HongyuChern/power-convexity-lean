import PowerConvexity.Calculus.AppendixCStrongMinimum
import PowerConvexity.Calculus.ScalarDirichlet
import PowerConvexity.Calculus.ScalarBasis
import PowerConvexity.Analysis.PositiveHessianAnchor

/-! # The fully closed a priori strictness step in Appendix C

This is the appendix's implication from convexity of the square-root transform
to positive real Hessian and the public strict chord inequality. The convexity
hypothesis remains explicit. The deformation argument needed to establish it
is not asserted in this module.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff Topology

namespace PowerConvexity
open CHS.Calculus

theorem scalarDirichlet_realHessian_pos_of_convex {U : Set ℂ} {u : ℂ → ℝ} {ρ : ℝ}
    (hU : IsOpen U) (hK : IsCompact (closure U))
    (huc : ContinuousOn u (closure U)) (hu : ContDiffOn ℝ 2 u U)
    (hboundary : ∀ x ∈ frontier U, u x = 0) (hρpos : 0 < ρ)
    (hρ : ∀ x ∈ U, complexHessian (fun _ : Fin 1 => (1 : ℂ))
      (fun _ : Fin 1 => Complex.I) u x 0 0 = (ρ : ℂ))
    (hconv : ConvexOn ℝ U (powerTransform u)) :
    ∀ x ∈ U, ∀ v : ℂ, v ≠ 0 → 0 < realHessian (powerTransform u) x v v := by
  have hneg := scalarDirichlet_negative hU hK huc hu hboundary hρpos hρ
  have hv := powerTransform_contDiffOn hu hneg
  have hσ : ∀ x ∈ U, 0 ≤ scalarSigma 1 Complex.I u x :=
    fun _ hx => scalarSigma_nonneg_of_convex_power hU hu hneg hconv 1 Complex.I hρpos hρ hx
  intro x hx
  have hanchor : ∃ y ∈ U, 0 < scalarSigma 1 Complex.I u y := by
    obtain ⟨y, hy, hH⟩ := exists_positive_realHessian_of_negative_zero_boundary hU hK
      (powerTransform_continuousOn huc) hv
      (fun y hy => powerTransform_eq_zero_of_eq_zero (hboundary y hy))
      ⟨x, hx, powerTransform_neg_of_neg (hneg x hx)⟩
    exact ⟨y, hy, (realHessian_power_scalar_quadratic_pos_iff
      (hu.contDiffAt (hU.mem_nhds hy)) (hneg y hy) hρpos (hρ y hy)).mp hH⟩
  have hspos := scalarSigma_positive_of_nonneg_and_anchor hU hconv.1.isPreconnected hu
    hρpos hneg hρ hσ hanchor x hx
  exact (realHessian_power_scalar_quadratic_pos_iff
    (hu.contDiffAt (hU.mem_nhds hx)) (hneg x hx) hρpos (hρ x hx)).mpr hspos

/-- Appendix C's a priori strict-convexity implication, with only classical
interior C2 and closure continuity assumptions. Convexity is still an input. -/
theorem appendixC_apriori_strictConvexOn {U : Set ℂ} {u : ℂ → ℝ} {ρ : ℝ}
    (hU : IsOpen U) (hK : IsCompact (closure U))
    (huc : ContinuousOn u (closure U)) (hu : ContDiffOn ℝ 2 u U)
    (hboundary : ∀ x ∈ frontier U, u x = 0) (hρpos : 0 < ρ)
    (hρ : ∀ x ∈ U, complexHessian (fun _ : Fin 1 => (1 : ℂ))
      (fun _ : Fin 1 => Complex.I) u x 0 0 = (ρ : ℂ))
    (hconv : ConvexOn ℝ U (powerTransform u)) :
    StrictConvexOn ℝ U (powerTransform u) := by
  apply strictConvexOn_of_realHessian_pos hU hconv.1
    (powerTransform_contDiffOn hu (scalarDirichlet_negative hU hK huc hu hboundary hρpos hρ))
  exact scalarDirichlet_realHessian_pos_of_convex hU hK huc hu hboundary hρpos hρ hconv

end PowerConvexity
