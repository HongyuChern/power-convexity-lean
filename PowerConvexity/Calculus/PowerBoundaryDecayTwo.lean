import PowerConvexity.Calculus.ConvexSupportedBallsReal
import PowerConvexity.Calculus.ScalarDirichlet

/-! # Actual Dirichlet boundary decay in complex dimension two -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ContDiff ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem strictPshDirichlet_nonpos_closure_two {U : Set E} {u : E → ℝ}
    (hU : IsOpen U) (hK : IsCompact (closure U))
    (huc : ContinuousOn u (closure U)) (hu : ContDiffOn ℝ 2 u U)
    (hboundary : ∀ x ∈ frontier U, u x = 0)
    (a b : Fin 2 → E) (hpsh : ∀ x ∈ U, (complexHessian a b u x).PosDef) :
    ∀ x ∈ closure U, u x ≤ 0 := by
  intro x hx
  by_cases hi : x ∈ U
  · exact (strictPshDirichlet_negative hU hK huc hu hboundary a b hpsh x hi).le
  · rw [hboundary x (by rw [hU.frontier_eq]; exact ⟨hx,hi⟩)]

theorem dirichlet_boundary_decay_two
    {U : Set E} {u : E → ℝ}
    (hU : IsOpen U) (hK : IsCompact (closure U))
    (huc : ContinuousOn u (closure U)) (hu : ContDiffOn ℝ 2 u U)
    (hboundary : ∀ x ∈ frontier U, u x = 0)
    (a b : Fin 2 → E) (hab : Orthonormal ℝ (Sum.elim a b))
    (hpsh : ∀ x ∈ U, (complexHessian a b u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian a b u x).det = 1)
    (hballs : HasSupportedInteriorBallReal U) :
    HasQuadraticBoundaryDecay (powerTransform u) U := by
  intro x hx y hy
  obtain ⟨c,R,hR,hball,hxr,hdir⟩ := hballs x hx
  exact power_boundary_decay_of_translated_ball hR (by norm_num : (0:ℝ) < 1) hball hxr (hdir y hy)
    (solution_le_translated_ball_two a b hab hR hball huc hu
      (strictPshDirichlet_nonpos_closure_two hU hK huc hu hboundary a b hpsh) hpsh hdet)

theorem dirichlet_boundary_decay_of_C2_boundary_two
    {U : Set E} {u : E → ℝ}
    (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hboundaryRegular : HasC2LocalDefiningFunction U)
    (huc : ContinuousOn u (closure U)) (hu : ContDiffOn ℝ 2 u U)
    (hboundary : ∀ x ∈ frontier U, u x = 0)
    (a b : Fin 2 → E) (hab : Orthonormal ℝ (Sum.elim a b))
    (hpsh : ∀ x ∈ U, (complexHessian a b u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian a b u x).det = 1) :
    HasQuadraticBoundaryDecay (powerTransform u) U :=
  dirichlet_boundary_decay_two hU hK huc hu hboundary a b hab hpsh hdet
    (convex_C2_boundary_supported_balls_real hU hconv hboundaryRegular)

end PowerConvexity
