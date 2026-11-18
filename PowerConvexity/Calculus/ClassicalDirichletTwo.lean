import PowerConvexity.Calculus.QuadraticBallPotential
import PowerConvexity.Calculus.StrictPshDirichlet

/-! # Comparison, uniqueness and uniform C0 barriers for classical solutions -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem classical_comparison_two {U : Set E} (hU : IsOpen U)
    (hK : IsCompact (closure U)) (a b : Fin 2 → E)
    (hab : Orthonormal ℝ (Sum.elim a b)) {u v : E → ℝ}
    (huc : ContinuousOn u (closure U)) (hvc : ContinuousOn v (closure U))
    (hu : ContDiffOn ℝ 2 u U) (hv : ContDiffOn ℝ 2 v U)
    (hAu : ∀ x ∈ U, (complexHessian a b u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian a b v x).det.re ≤ (complexHessian a b u x).det.re)
    (hb : ∀ x ∈ frontier U, u x ≤ v x) : ∀ x ∈ closure U, u x ≤ v x := by
  obtain ⟨R,hR,hbound⟩ := hK.isBounded.exists_pos_norm_le
  apply classical_comparison_two_with_quadratic hU hK a b huc hvc hu hv hAu hdet hb
    (ψ := quadraticBallPotential 1 R)
    (quadraticBallPotential_contDiff 1 R 0).continuous.continuousOn
    (quadraticBallPotential_contDiff 1 R 2).contDiffOn
  · intro x hx
    have hxR := hbound x (frontier_subset_closure hx)
    have hs : ‖x‖^2 ≤ R^2 := pow_le_pow_left₀ (norm_nonneg x) hxR 2
    simp only [quadraticBallPotential,one_mul]
    linarith
  · intro x hx
    simpa using quadraticBallPotential_complexHessian a b hab 1 R x

theorem classical_dirichlet_unique_two {U : Set E} (hU : IsOpen U)
    (hK : IsCompact (closure U)) (a b : Fin 2 → E)
    (hab : Orthonormal ℝ (Sum.elim a b)) {u v : E → ℝ}
    (huc : ContinuousOn u (closure U)) (hvc : ContinuousOn v (closure U))
    (hu : ContDiffOn ℝ 2 u U) (hv : ContDiffOn ℝ 2 v U)
    (hAu : ∀ x ∈ U, (complexHessian a b u x).PosDef)
    (hAv : ∀ x ∈ U, (complexHessian a b v x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian a b u x).det = (complexHessian a b v x).det)
    (hb : EqOn u v (frontier U)) : EqOn u v (closure U) := by
  have huv := classical_comparison_two hU hK a b hab huc hvc hu hv hAu
    (fun x hx => le_of_eq (congrArg Complex.re (hdet x hx).symm))
    (fun x hx => (hb hx).le)
  have hvu := classical_comparison_two hU hK a b hab hvc huc hv hu hAv
    (fun x hx => le_of_eq (congrArg Complex.re (hdet x hx)))
    (fun x hx => (hb hx).ge)
  exact fun x hx => le_antisymm (huv x hx) (hvu x hx)

/-- An explicit lower barrier with a fixed encompassing ball and density
bound.  It supplies the common negative lower bound needed in C12. -/
theorem classical_dirichlet_lower_barrier_two {U : Set E} (hU : IsOpen U)
    (hK : IsCompact (closure U)) (a b : Fin 2 → E)
    (hab : Orthonormal ℝ (Sum.elim a b)) {u : E → ℝ} {c R : ℝ}
    (hc : 0 < c) (hR : 0 < R) (hbound : ∀ x ∈ closure U, ‖x‖ ≤ R)
    (huc : ContinuousOn u (closure U)) (hu : ContDiffOn ℝ 2 u U)
    (hdet : ∀ x ∈ U, (complexHessian a b u x).det.re < c^2)
    (hb : ∀ x ∈ frontier U, 0 ≤ u x) : ∀ x ∈ closure U, -c*R^2 ≤ u x := by
  have hcomp : ∀ x ∈ closure U, quadraticBallPotential c R x ≤ u x := by
    apply classical_strict_comparison_two hU hK a b
      (quadraticBallPotential_contDiff c R 0).continuous.continuousOn huc
      (quadraticBallPotential_contDiff c R 2).contDiffOn hu
    · intro x hx
      rw [quadraticBallPotential_complexHessian a b hab]
      exact posDef_real_smul Matrix.PosDef.one hc
    · intro x hx
      rw [quadraticBallPotential_det_two a b hab,Complex.ofReal_re]
      exact hdet x hx
    · intro x hx
      have hxR := hbound x (frontier_subset_closure hx)
      have hs := pow_le_pow_left₀ (norm_nonneg x) hxR 2
      have hprod := mul_nonpos_of_nonneg_of_nonpos hc.le (sub_nonpos.mpr hs)
      exact hprod.trans (hb x hx)
  intro x hx
  have hq := hcomp x hx
  have hpos := mul_nonneg hc.le (sq_nonneg ‖x‖)
  dsimp [quadraticBallPotential] at hq
  nlinarith

/-- The explicit starting solution on a ball, including the strict psh branch
and the public strict-convexity conclusion for the power transform. -/
theorem quadraticBallPotential_classical_solution_two
    (a b : Fin 2 → E) (hab : Orthonormal ℝ (Sum.elim a b))
    {ρ R : ℝ} (hρ : 0 < ρ) (hR : 0 < R) :
    (∀ x, (complexHessian a b (quadraticBallPotential (Real.sqrt ρ) R) x).det = (ρ:ℂ)) ∧
    (∀ x, (complexHessian a b (quadraticBallPotential (Real.sqrt ρ) R) x).PosDef) ∧
    (∀ x ∈ sphere (0:E) R, quadraticBallPotential (Real.sqrt ρ) R x = 0) ∧
    StrictConvexOn ℝ (ball (0:E) R)
      (powerTransform (quadraticBallPotential (Real.sqrt ρ) R)) := by
  have hc : 0 < Real.sqrt ρ := Real.sqrt_pos.mpr hρ
  refine ⟨?_,?_,?_,quadraticBallPotential_strictConvexOn hc hR⟩
  · intro x
    rw [quadraticBallPotential_det_two a b hab,Real.sq_sqrt hρ.le]
  · intro x
    rw [quadraticBallPotential_complexHessian a b hab]
    exact posDef_real_smul Matrix.PosDef.one hc
  · intro x hx
    exact quadraticBallPotential_boundary _ _ hx

theorem quadraticBallPotential_frontier {c R : ℝ} (hR : 0 < R) :
    ∀ x ∈ frontier (ball (0:E) R), quadraticBallPotential c R x = 0 := by
  rw [frontier_ball 0 hR.ne']
  exact fun x hx => quadraticBallPotential_boundary c R hx

theorem classicalDirichlet_ball_identification_two [ProperSpace E]
    (a b : Fin 2 → E) (hab : Orthonormal ℝ (Sum.elim a b))
    {ρ R : ℝ} (hρ : 0 < ρ) (hR : 0 < R) {u : E → ℝ}
    (huc : ContinuousOn u (closure (ball 0 R)))
    (hu : ContDiffOn ℝ 2 u (ball 0 R))
    (hAu : ∀ x ∈ ball 0 R, (complexHessian a b u x).PosDef)
    (hdet : ∀ x ∈ ball 0 R, (complexHessian a b u x).det = (ρ:ℂ))
    (hb : ∀ x ∈ frontier (ball 0 R), u x = 0) :
    EqOn u (quadraticBallPotential (Real.sqrt ρ) R) (closure (ball 0 R)) := by
  obtain ⟨hD,hA,hB,hS⟩ := quadraticBallPotential_classical_solution_two a b hab hρ hR
  apply classical_dirichlet_unique_two isOpen_ball
    (by rw [closure_ball 0 hR.ne']; exact isCompact_closedBall _ _) a b hab
    huc (quadraticBallPotential_contDiff (Real.sqrt ρ) R 0).continuous.continuousOn
    hu (quadraticBallPotential_contDiff (Real.sqrt ρ) R 2).contDiffOn hAu
    (fun x _ => hA x)
  · intro x hx
    rw [hdet x hx,hD x]
  · intro x hx
    rw [hb x hx,quadraticBallPotential_frontier hR x hx]

end PowerConvexity
