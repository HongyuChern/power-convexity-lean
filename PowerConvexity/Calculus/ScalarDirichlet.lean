import PowerConvexity.Analysis.StrictSubharmonicMaximum
import PowerConvexity.Calculus.ScalarInteriorRegularity

/-! # Negativity and interior smoothness of a scalar classical Dirichlet solution -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff Topology

namespace PowerConvexity
open CHS.Calculus

theorem scalarDirichlet_negative {U : Set ℂ} {u : ℂ → ℝ} {ρ : ℝ}
    (hU : IsOpen U) (hK : IsCompact (closure U))
    (huc : ContinuousOn u (closure U)) (hu : ContDiffOn ℝ 2 u U)
    (hboundary : ∀ x ∈ frontier U, u x = 0) (hρpos : 0 < ρ)
    (hρ : ∀ x ∈ U, complexHessian (fun _ : Fin 1 => (1 : ℂ))
      (fun _ : Fin 1 => Complex.I) u x 0 0 = (ρ : ℂ)) :
    ∀ x ∈ U, u x < 0 := by
  apply negative_of_positive_hessian_contraction hU hK huc hu hboundary
    (fun _ => scalarHessianContraction) (fun _ _ => scalarHessianContraction_positive)
  intro x hx
  rw [scalarContraction_eq_mixed_re (hu.contDiffAt (hU.mem_nhds hx)), hρ x hx,
    Complex.ofReal_re]
  exact hρpos

theorem scalarDirichlet_contDiffOn {U : Set ℂ} {u : ℂ → ℝ} {ρ : ℝ}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U)
    (hρ : ∀ x ∈ U, complexHessian (fun _ : Fin 1 => (1 : ℂ))
      (fun _ : Fin 1 => Complex.I) u x 0 0 = (ρ : ℂ)) (n : WithTop ℕ∞) :
    ContDiffOn ℝ n u U := by
  intro x hx
  apply ContDiffAt.contDiffWithinAt
  apply scalar_constDensity_contDiffAt (ρ := ρ) (hu.contDiffAt (hU.mem_nhds hx)) _ n
  exact Filter.Eventually.mono (hU.mem_nhds hx) fun y hy => hρ y hy

theorem powerTransform_continuousOn {E : Type*} [TopologicalSpace E]
    {u : E → ℝ} {S : Set E} (hu : ContinuousOn u S) :
    ContinuousOn (powerTransform u) S := by
  exact hu.neg.sqrt.neg

theorem powerTransform_eq_zero_of_eq_zero {E : Type*} {u : E → ℝ} {x : E}
    (hu : u x = 0) : powerTransform u x = 0 := by
  simp [powerTransform, negativeSqrt, hu]

theorem powerTransform_neg_of_neg {E : Type*} {u : E → ℝ} {x : E}
    (hu : u x < 0) : powerTransform u x < 0 := by
  exact neg_neg_of_pos (Real.sqrt_pos.mpr (neg_pos.mpr hu))

end PowerConvexity
