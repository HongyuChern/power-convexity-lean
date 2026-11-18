import PowerConvexity.Calculus.MinkowskiActualTangentBall
import PowerConvexity.Calculus.VariableDensityBoundaryNormalTwo

/-! # A uniform actual boundary gradient lower bound near the ball endpoint.
This is a lower bound, not the still-missing upper bound or full Hessian
estimate. It holds for every actual classical solution with determinant
at least one, using the actual closure derivative.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

theorem classicalDirichlet_boundary_gradient_lower_of_tangent_ball_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U)
    (hb : ∀ x ∈ frontier U, u x = 0)
    (a b : Fin 2 → E) (hab : Orthonormal ℝ (Sum.elim a b))
    (hpsh : ∀ x ∈ U, (complexHessian a b u x).PosDef)
    (hdet : ∀ x ∈ U, (1 : ℝ) ≤ (complexHessian a b u x).det.re)
    {x c : E} {R : ℝ} (hx : x ∈ frontier U) (hR : 0 < R)
    (hball : ball c R ⊆ U) (hxr : ‖x-c‖ = R) :
    2*R ≤ ‖J.derivative x‖ := by
  have hh := classicalDirichlet_inward_ball_derivative_of_det_lower_two
    hU hconv hK hu J hb a b hab hpsh hdet hx hR hball hxr
  have hn := (J.derivative x).le_opNorm (c-x)
  rw [norm_sub_rev c x,hxr,Real.norm_eq_abs] at hn
  have hneg : 0 ≤ -(J.derivative x (c-x)) := by nlinarith [sq_nonneg R]
  have hl : -(J.derivative x (c-x)) ≤ ‖J.derivative x‖*R :=
    (neg_le_abs _).trans hn
  apply (mul_le_mul_iff_left₀ hR).mp
  nlinarith only [hh,hl]

theorem minkowski_actual_solution_boundary_gradient_lower_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hboundary : HasC2LocalDefiningFunction U)
    {t R : ℝ} (ht : 0 < t) (ht1 : t < 1) (hR : 0 < R)
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u (minkowskiDomain t U (ball (0 : E) R)))
    (J : ClosureC2Jet u (minkowskiDomain t U (ball (0 : E) R)))
    (hb : ∀ x ∈ frontier (minkowskiDomain t U (ball (0 : E) R)), u x = 0)
    (a b : Fin 2 → E) (hab : Orthonormal ℝ (Sum.elim a b))
    (hpsh : ∀ x ∈ minkowskiDomain t U (ball (0 : E) R), (complexHessian a b u x).PosDef)
    (hdet : ∀ x ∈ minkowskiDomain t U (ball (0 : E) R),
      (1 : ℝ) ≤ (complexHessian a b u x).det.re) :
    ∀ y ∈ frontier (minkowskiDomain t U (ball (0 : E) R)),
      2*((1-t)*R) ≤ ‖J.derivative y‖ := by
  have hVo : IsOpen (minkowskiDomain t U (ball (0 : E) R)) := by
    rw [minkowskiDomain_eq_smul_add]
    exact (hU.smul₀ ht.ne').add_right
  have hVc := minkowskiDomain_convex hconv (convex_ball (0 : E) R) t
  have hBK : IsCompact (closure (ball (0 : E) R)) := by
    rw [closure_ball 0 hR.ne']
    exact isCompact_closedBall 0 R
  have hVK : IsCompact (closure (minkowskiDomain t U (ball (0 : E) R))) := by
    rw [minkowskiDomain_closure hK hBK]
    exact (hK.smul t).add (hBK.smul (1-t))
  intro y hy
  obtain ⟨c,hball,hyr⟩ := minkowski_frontier_actual_tangent_ball
    hU hconv hK hboundary ht ht1 hR hy
  exact classicalDirichlet_boundary_gradient_lower_of_tangent_ball_two
    hVo hVc hVK hu J hb a b hab hpsh hdet hy
    (mul_pos (sub_pos.mpr ht1) hR) hball hyr

theorem minkowski_actual_solution_boundary_gradient_lower_near_zero_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hboundary : HasC2LocalDefiningFunction U)
    {t R : ℝ} (ht : 0 < t) (htHalf : t ≤ 1/2) (hR : 0 < R)
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u (minkowskiDomain t U (ball (0 : E) R)))
    (J : ClosureC2Jet u (minkowskiDomain t U (ball (0 : E) R)))
    (hb : ∀ x ∈ frontier (minkowskiDomain t U (ball (0 : E) R)), u x = 0)
    (a b : Fin 2 → E) (hab : Orthonormal ℝ (Sum.elim a b))
    (hpsh : ∀ x ∈ minkowskiDomain t U (ball (0 : E) R), (complexHessian a b u x).PosDef)
    (hdet : ∀ x ∈ minkowskiDomain t U (ball (0 : E) R),
      (1 : ℝ) ≤ (complexHessian a b u x).det.re) :
    ∀ y ∈ frontier (minkowskiDomain t U (ball (0 : E) R)), R ≤ ‖J.derivative y‖ := by
  intro y hy
  have hh := minkowski_actual_solution_boundary_gradient_lower_two
    hU hconv hK hboundary ht (by linarith : t < 1) hR hu J hb a b hab hpsh hdet y hy
  nlinarith only [hh,mul_le_mul_of_nonneg_right htHalf hR.le]

end PowerConvexity
