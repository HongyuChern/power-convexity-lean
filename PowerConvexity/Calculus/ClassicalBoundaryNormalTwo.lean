import PowerConvexity.Calculus.ClosureJetDifferentiability
import PowerConvexity.Calculus.PowerBoundaryDecayTwo
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! # Nonvanishing of the actual classical boundary derivative

An interior tangent ball and the already proved CMA comparison give a
quantitative inward derivative inequality for the prescribed closure jet.
This is derived from the actual PDE, not assumed as a boundary condition.
It requires no real curvature lower bound and no power-convexity theorem.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric Filter
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem translatedBallPotential_fderiv_apply (s R : ℝ) (c x v : E) :
    fderiv ℝ (translatedBallPotential s R c) x v = 2*s*inner ℝ (x-c) v := by
  have hd := ((((hasFDerivAt_id (𝕜 := ℝ) (x := x)).sub_const c).norm_sq).sub_const (R^2)).const_mul s
  change HasFDerivAt (translatedBallPotential s R c) _ x at hd
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply,innerSL_apply_apply,id_eq,smul_eq_mul]
  ring

theorem classicalDirichlet_inward_ball_derivative_le_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U)
    (hb : ∀ x ∈ frontier U, u x = 0)
    (a b : Fin 2 → E) (hab : Orthonormal ℝ (Sum.elim a b))
    (hpsh : ∀ x ∈ U, (complexHessian a b u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian a b u x).det = 1)
    {x c : E} {R : ℝ} (hx : x ∈ frontier U) (hR : 0 < R)
    (hball : ball c R ⊆ U) (hxr : ‖x-c‖ = R) :
    J.derivative x (c-x) ≤ -2*R^2 := by
  have hcomp := solution_le_translated_ball_two a b hab hR hball J.continuous_value hu
    (strictPshDirichlet_nonpos_closure_two hU hK J.continuous_value hu hb a b hpsh) hpsh hdet
  have hxball : x ∈ closure (ball c R) := by
    rw [closure_ball c hR.ne',mem_closedBall,dist_eq_norm,hxr]
  have hcball : c ∈ closure (ball c R) := subset_closure (mem_ball_self hR)
  have hcone : c-x ∈ posTangentConeAt (closure (ball c R)) x :=
    sub_mem_posTangentConeAt_of_segment_subset
      ((convex_ball c R).closure.segment_subset hxball hcball)
  have hD : HasFDerivWithinAt u (J.derivative x) (closure (ball c R)) x :=
    (closureJet_hasFDerivWithinAt hU hconv (hu.differentiableOn (by norm_num)) J
      (frontier_subset_closure hx)).mono (closure_mono hball)
  have hmax : IsMaxOn (fun y => u y-translatedBallPotential 1 R c y) (closure (ball c R)) x := by
    intro y hy
    change u y-translatedBallPotential 1 R c y ≤ u x-translatedBallPotential 1 R c x
    rw [hb x hx,translatedBallPotential_zero_on_sphere 1 R c x hxr,sub_self]
    exact sub_nonpos.mpr (hcomp y hy)
  have hv := ((translatedBallPotential_contDiff 1 R c 1).differentiable (by norm_num) x).hasFDerivAt
  have hh := hmax.localize.hasFDerivWithinAt_nonpos (hD.sub hv.hasFDerivWithinAt) hcone
  change J.derivative x (c-x)-fderiv ℝ (translatedBallPotential 1 R c) x (c-x) ≤ 0 at hh
  rw [translatedBallPotential_fderiv_apply] at hh
  have hi : inner ℝ (x-c) (c-x) = -(R^2) := by
    rw [show c-x = -(x-c) by abel,inner_neg_right,real_inner_self_eq_norm_sq,hxr]
  rw [hi] at hh
  linarith

theorem classicalDirichlet_boundary_derivative_ne_zero_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hboundaryRegular : HasC2LocalDefiningFunction U)
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U)
    (hb : ∀ x ∈ frontier U, u x = 0)
    (a b : Fin 2 → E) (hab : Orthonormal ℝ (Sum.elim a b))
    (hpsh : ∀ x ∈ U, (complexHessian a b u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian a b u x).det = 1) :
    ∀ x ∈ frontier U, J.derivative x ≠ 0 := by
  intro x hx
  obtain ⟨c,R,hR,hball,hxr,_⟩ :=
    convex_C2_boundary_supported_balls_real hU hconv hboundaryRegular x hx
  have hh := classicalDirichlet_inward_ball_derivative_le_two hU hconv hK hu J hb a b hab
    hpsh hdet hx hR hball hxr
  intro hz
  rw [hz,ContinuousLinearMap.zero_apply] at hh
  nlinarith [sq_pos_of_pos hR]

end PowerConvexity
