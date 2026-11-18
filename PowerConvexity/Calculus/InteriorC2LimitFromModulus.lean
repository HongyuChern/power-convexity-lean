import PowerConvexity.Analysis.CompactModulusSequence
import PowerConvexity.Calculus.ClosureJetC1Compactness

/-! # Identification of the actual second derivative of a C1 limit.
A bounded common spatial Hessian modulus gives a uniform subsequence on a
compact interior ball. Passing the derivative identity to the limit proves
actual C2 regularity and identifies the Hessian, not just a matrix field.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem interior_C2_limit_of_first_derivative_convergence_and_hessian_modulus
    {U : Set E} (hU : IsOpen U) (u : ℕ → E → ℝ)
    (hu : ∀ n, ContDiffOn ℝ 2 (u n) U)
    {g : E → ℝ} {D : E → E →L[ℝ] ℝ}
    (hgD : ∀ x ∈ U, HasFDerivAt g (D x) x)
    (hDlim : ∀ x ∈ U, Tendsto (fun n => fderiv ℝ (u n) x) atTop (𝓝 (D x)))
    {x₀ : E} {R M : ℝ} (hR : 0 < R) (hclosed : closedBall x₀ R ⊆ U)
    (hbound : ∀ n x, x ∈ closedBall x₀ R → ‖realHessian (u n) x‖ ≤ M)
    (omega : ℝ → ℝ) (homega : Tendsto omega (𝓝 0) (𝓝 0))
    (hmod : ∀ n x, x ∈ closedBall x₀ R → ∀ y, y ∈ closedBall x₀ R →
      ‖realHessian (u n) x-realHessian (u n) y‖ ≤ omega ‖x-y‖) :
    ContDiffOn ℝ 2 g (ball x₀ R) ∧
      ∃ phi : ℕ → ℕ, StrictMono phi ∧
        TendstoUniformlyOn (fun n => realHessian (u (phi n))) (realHessian g) atTop (ball x₀ R) ∧
        (∀ x ∈ ball x₀ R, ‖realHessian g x‖ ≤ M) ∧
        ∀ x ∈ ball x₀ R, ∀ y ∈ ball x₀ R,
          ‖realHessian g x-realHessian g y‖ ≤ omega ‖x-y‖ := by
  have hcont (n : ℕ) : ContinuousOn (realHessian (u n)) (closedBall x₀ R) := by
    intro x hx
    have hc := (hu n).contDiffAt (hU.mem_nhds (hclosed hx))
    exact (((hc.fderiv_right (m := 1) (by norm_num)).fderiv_right
      (m := 0) (by norm_num)).continuousAt).continuousWithinAt
  obtain ⟨phi,hphi,H,hHc,hHunif,hHb,hHm⟩ :=
    compact_modulus_sequence_has_uniform_subsequence (isCompact_closedBall x₀ R)
      (fun n => realHessian (u n)) hcont M hbound omega homega
      (fun n x hx y hy => by simpa only [dist_eq_norm] using hmod n x hx y hy)
  have hball : ball x₀ R ⊆ U := ball_subset_closedBall.trans hclosed
  have hDH (x : E) (hx : x ∈ ball x₀ R) : HasFDerivAt D (H x) x := by
    apply hasFDerivAt_of_tendstoUniformlyOn isOpen_ball (hHunif.mono ball_subset_closedBall)
      (f := fun n => fderiv ℝ (u (phi n)))
    · intro n y hy
      exact (((hu (phi n)).contDiffAt (hU.mem_nhds (hball hy))).fderiv_right
        (m := 1) (by norm_num)).differentiableAt (by norm_num) |>.hasFDerivAt
    · intro y hy
      exact (hDlim y (hball hy)).comp hphi.tendsto_atTop
    · exact hx
  have hD1 : ContDiffOn ℝ 1 D (ball x₀ R) := by
    rw [show (1 : ℕ∞ω) = 0+1 by norm_num]
    exact (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn isOpen_ball.uniqueDiffOn).mpr
      ⟨by simp,H,contDiffOn_zero.mpr (hHc.mono ball_subset_closedBall),
        fun x hx => (hDH x hx).hasFDerivWithinAt⟩
  have hg2 : ContDiffOn ℝ 2 g (ball x₀ R) := by
    rw [show (2 : ℕ∞ω) = 1+1 by norm_num]
    exact (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn isOpen_ball.uniqueDiffOn).mpr
      ⟨by simp,D,hD1,fun x hx => (hgD x (hball hx)).hasFDerivWithinAt⟩
  have hGeq (x : E) (hx : x ∈ ball x₀ R) : realHessian g x = H x := by
    have heq : fderiv ℝ g =ᶠ[𝓝 x] D := by
      filter_upwards [hU.mem_nhds (hball hx)] with y hy
      exact (hgD y hy).fderiv
    change fderiv ℝ (fderiv ℝ g) x = H x
    rw [heq.fderiv_eq]
    exact (hDH x hx).fderiv
  refine ⟨hg2,phi,hphi,(hHunif.mono ball_subset_closedBall).congr_right
    (fun x hx => (hGeq x hx).symm),?_,?_⟩
  · intro x hx
    rw [hGeq x hx]
    exact hHb x (ball_subset_closedBall hx)
  · intro x hx y hy
    rw [hGeq x hx,hGeq y hy]
    simpa only [dist_eq_norm] using hHm x (ball_subset_closedBall hx) y (ball_subset_closedBall hy)

end PowerConvexity
