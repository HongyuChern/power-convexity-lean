import PowerConvexity.Calculus.ScalarWeakComparison
import CHS.Calculus.AffinePullback

/-! # Actual scalar Dirichlet comparison with a tangent ball potential -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus

noncomputable def scalarBallBarrier (ρ R : ℝ) (c z : ℂ) : ℝ :=
  quadraticBallPotential ρ R (z-c)

theorem scalarBallBarrier_contDiff (ρ R : ℝ) (c : ℂ) (n : ℕ∞ω) :
    ContDiff ℝ n (scalarBallBarrier ρ R c) :=
  (quadraticBallPotential_contDiff ρ R n).comp (contDiff_id.sub contDiff_const)

theorem scalarBallBarrier_realHessian (ρ R : ℝ) (c x v w : ℂ) :
    realHessian (scalarBallBarrier ρ R c) x v w = 2*ρ*inner ℝ v w := by
  have he : scalarBallBarrier ρ R c = fun y =>
      quadraticBallPotential ρ R (-c+(ContinuousLinearMap.id ℝ ℂ) y) := by
    funext y
    simp only [scalarBallBarrier,ContinuousLinearMap.id_apply,sub_eq_add_neg,add_comm]
  rw [he,realHessian_comp_affine (ContinuousLinearMap.id ℝ ℂ) (-c)
    (quadraticBallPotential_contDiff ρ R 2).contDiffAt]
  exact quadraticBallPotential_realHessian ρ R _ _ _

theorem scalarBallBarrier_contraction (ρ R : ℝ) (c x : ℂ) :
    scalarHessianContraction (realHessian (scalarBallBarrier ρ R c) x) = ρ := by
  change (realHessian (scalarBallBarrier ρ R c) x 1 1+
    realHessian (scalarBallBarrier ρ R c) x Complex.I Complex.I)/4 = ρ
  rw [scalarBallBarrier_realHessian,scalarBallBarrier_realHessian]
  simp only [real_inner_self_eq_norm_sq,norm_one,Complex.norm_I]
  ring

theorem scalarBallBarrier_zero_on_sphere (ρ R : ℝ) (c x : ℂ) (hx : ‖x-c‖ = R) :
    scalarBallBarrier ρ R c x = 0 := by
  simp only [scalarBallBarrier,quadraticBallPotential,hx,sub_self,mul_zero]

theorem scalar_solution_le_ball_barrier
    {U : Set ℂ} {u : ℂ → ℝ} {ρ R : ℝ} {c : ℂ}
    (hR : 0 < R) (hball : ball c R ⊆ U)
    (huc : ContinuousOn u (closure U)) (hu : ContDiffOn ℝ 2 u U)
    (hnonpos : ∀ x ∈ closure U, u x ≤ 0)
    (hρ : ∀ x ∈ U, complexHessian (fun _ : Fin 1 => (1:ℂ))
      (fun _ : Fin 1 => Complex.I) u x 0 0 = (ρ:ℂ)) :
    ∀ x ∈ closure (ball c R), u x ≤ scalarBallBarrier ρ R c x := by
  have hcl : closure (ball c R) ⊆ closure U := closure_mono hball
  have hcompact : IsCompact (closure (ball c R)) := by
    rw [closure_ball c hR.ne']
    exact isCompact_closedBall c R
  apply scalar_comparison_on_closure isOpen_ball hcompact (huc.mono hcl)
    (scalarBallBarrier_contDiff ρ R c 0).continuous.continuousOn (hu.mono hball)
    (scalarBallBarrier_contDiff ρ R c 2).contDiffOn
  · intro x hx
    have hs : x ∈ sphere c R := by rwa [frontier_ball c hR.ne'] at hx
    have hn : ‖x-c‖ = R := by simpa only [mem_sphere,dist_eq_norm] using hs
    rw [scalarBallBarrier_zero_on_sphere ρ R c x hn]
    exact hnonpos x (hcl (frontier_subset_closure hx))
  · intro x hx
    rw [scalarBallBarrier_contraction,scalarContraction_eq_mixed_re
      ((hu.mono hball).contDiffAt (isOpen_ball.mem_nhds hx)),hρ x (hball hx),Complex.ofReal_re]

end PowerConvexity
