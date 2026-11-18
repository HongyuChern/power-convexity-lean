import PowerConvexity.Calculus.InteriorC2LimitFromModulus

/-! # Identification of actual Banach-valued derivatives in a compact limit -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace PowerConvexity
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

theorem actual_interior_C1_limit_of_derivative_modulus
    {U : Set E} (hU : IsOpen U) (f : ℕ → E → V)
    (hf : ∀ n, ContDiffOn ℝ 1 (f n) U) {g : E → V}
    (hlim : ∀ x ∈ U, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    {x₀ : E} {R M : ℝ} (hR : 0 < R) (hclosed : closedBall x₀ R ⊆ U)
    (hbound : ∀ n x, x ∈ closedBall x₀ R → ‖fderiv ℝ (f n) x‖ ≤ M)
    (omega : ℝ → ℝ) (homega : Tendsto omega (𝓝 0) (𝓝 0))
    (hmod : ∀ n x, x ∈ closedBall x₀ R → ∀ y, y ∈ closedBall x₀ R →
      ‖fderiv ℝ (f n) x-fderiv ℝ (f n) y‖ ≤ omega ‖x-y‖) :
    ContDiffOn ℝ 1 g (ball x₀ R) ∧
      ∃ phi : ℕ → ℕ, StrictMono phi ∧
        TendstoUniformlyOn (fun n => fderiv ℝ (f (phi n))) (fderiv ℝ g) atTop (ball x₀ R) ∧
        (∀ x ∈ ball x₀ R, ‖fderiv ℝ g x‖ ≤ M) ∧
        ∀ x ∈ ball x₀ R, ∀ y ∈ ball x₀ R,
          ‖fderiv ℝ g x-fderiv ℝ g y‖ ≤ omega ‖x-y‖ := by
  have hcont (n : ℕ) : ContinuousOn (fderiv ℝ (f n)) (closedBall x₀ R) := by
    intro x hx
    exact (((hf n).contDiffAt (hU.mem_nhds (hclosed hx))).fderiv_right
      (m := 0) (by norm_num)).continuousAt.continuousWithinAt
  obtain ⟨phi,hphi,H,hHc,hHunif,hHb,hHm⟩ :=
    compact_modulus_sequence_has_uniform_subsequence (isCompact_closedBall x₀ R)
      (fun n => fderiv ℝ (f n)) hcont M hbound omega homega
      (fun n x hx y hy => by simpa only [dist_eq_norm] using hmod n x hx y hy)
  have hball : ball x₀ R ⊆ U := ball_subset_closedBall.trans hclosed
  have hgH (x : E) (hx : x ∈ ball x₀ R) : HasFDerivAt g (H x) x := by
    apply hasFDerivAt_of_tendstoUniformlyOn isOpen_ball (hHunif.mono ball_subset_closedBall)
      (f := fun n => f (phi n))
    · intro n y hy
      exact ((hf (phi n)).contDiffAt (hU.mem_nhds (hball hy))).differentiableAt
        (by norm_num) |>.hasFDerivAt
    · intro y hy
      exact (hlim y (hball hy)).comp hphi.tendsto_atTop
    · exact hx
  have hg1 : ContDiffOn ℝ 1 g (ball x₀ R) := by
    rw [show (1 : ℕ∞ω) = 0+1 by norm_num]
    exact (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn isOpen_ball.uniqueDiffOn).mpr
      ⟨by simp,H,contDiffOn_zero.mpr (hHc.mono ball_subset_closedBall),
        fun x hx => (hgH x hx).hasFDerivWithinAt⟩
  refine ⟨hg1,phi,hphi,(hHunif.mono ball_subset_closedBall).congr_right
    (fun x hx => (hgH x hx).fderiv.symm),?_,?_⟩
  · intro x hx
    rw [(hgH x hx).fderiv]
    exact hHb x (ball_subset_closedBall hx)
  · intro x hx y hy
    rw [(hgH x hx).fderiv,(hgH y hy).fderiv]
    simpa only [dist_eq_norm] using hHm x (ball_subset_closedBall hx) y (ball_subset_closedBall hy)

end PowerConvexity
