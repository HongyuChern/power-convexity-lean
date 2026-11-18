import PowerConvexity.Calculus.ViscosityHarmonicBallComparisonTwo
import PowerConvexity.Calculus.ViscosityHarmonicClassicalConsistencyTwo

/-! # Actual harmonic replacement and radial uniqueness on a ball.
These consequences are used to normalize an actual Poisson integral.
Existence or regularity of a harmonic extension is not assumed here as
an external theorem: the replacement comparison has its explicit classical
function as an argument.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open Set Filter Metric Matrix
open scoped ContDiff Topology BigOperators
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
local notation "E" => DeGiorgi.AmbientSpace (2+2)

theorem actual_classical_harmonic_trace_zero_two
    {p : E → ℝ} {U : Set E} (hp : InnerProductSpace.HarmonicOnNhd p U)
    {x : E} (hx : x ∈ U) :
    (realBlockHessian realDirections imagDirections p x).trace = 0 := by
  rw [actual_block_trace_eq_laplacian_two]
  exact (hp x hx).2.self_of_nhds

theorem viscosity_harmonic_classical_boundary_error_on_ball_two
    {g p : E → ℝ} {c : E} {R δ : ℝ} (hR : 0 < R)
    (hgc : ContinuousOn g (closedBall c R)) (hg : IsViscosityHarmonicTwo g (ball c R))
    (hpc : ContinuousOn p (closedBall c R))
    (hp : InnerProductSpace.HarmonicOnNhd p (ball c R))
    (hboundary : ∀ x ∈ sphere c R, |g x-p x| ≤ δ) :
    ∀ x ∈ closedBall c R, |g x-p x| ≤ δ := by
  have ht (x : E) (hx : x ∈ ball c R) := actual_classical_harmonic_trace_zero_two hp hx
  have hu : ∀ x ∈ closedBall c R, g x ≤ p x+δ :=
    viscosity_harmonic_le_classical_superharmonic_on_ball_two hR hgc hg
      (hpc.add continuousOn_const) (hp.contDiffOn.add contDiffOn_const)
      (by intro x hx; simpa only [realBlockHessian_add_const,ht x hx] using (le_refl (0:ℝ)))
      (by intro x hx; have h := (abs_le.mp (hboundary x hx)).2; linarith)
  have hl : ∀ x ∈ closedBall c R, p x+(-δ) ≤ g x :=
    classical_subharmonic_le_viscosity_harmonic_on_ball_two hR hgc hg
      (hpc.add continuousOn_const) (hp.contDiffOn.add contDiffOn_const)
      (by intro x hx; simpa only [realBlockHessian_add_const,ht x hx] using (le_refl (0:ℝ)))
      (by intro x hx; have h := (abs_le.mp (hboundary x hx)).1; linarith)
  intro x hx
  exact abs_le.mpr ⟨by linarith [hl x hx],by linarith [hu x hx]⟩

theorem viscosity_harmonic_eq_classical_on_ball_two
    {g p : E → ℝ} {c : E} {R : ℝ} (hR : 0 < R)
    (hgc : ContinuousOn g (closedBall c R)) (hg : IsViscosityHarmonicTwo g (ball c R))
    (hpc : ContinuousOn p (closedBall c R))
    (hp : InnerProductSpace.HarmonicOnNhd p (ball c R))
    (hboundary : ∀ x ∈ sphere c R, g x = p x) :
    EqOn g p (closedBall c R) := by
  have he := viscosity_harmonic_classical_boundary_error_on_ball_two hR hgc hg hpc hp
    (δ := 0) (by intro x hx; rw [hboundary x hx,sub_self,abs_zero])
  intro x hx
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm (he x hx) (abs_nonneg _)))

theorem actual_radial_classical_harmonic_constant_two
    {g : E → ℝ} {c : E} {R : ℝ}
    (hg : InnerProductSpace.HarmonicOnNhd g (ball c R))
    (hradial : ∀ x ∈ ball c R, ∀ y ∈ ball c R,
      dist x c = dist y c → g x = g y) :
    ∀ x ∈ ball c R, g x = g c := by
  intro x hx
  by_cases he : x = c
  · rw [he]
  have hr : 0 < dist x c := dist_pos.mpr he
  have hrR : dist x c < R := mem_ball.mp hx
  have hsub : closedBall c (dist x c) ⊆ ball c R := by
    intro y hy
    exact mem_ball.mpr ((mem_closedBall.mp hy).trans_lt hrR)
  have hgsmall : InnerProductSpace.HarmonicOnNhd g (ball c (dist x c)) := by
    intro y hy
    exact hg y (hsub (ball_subset_closedBall hy))
  have hEq := viscosity_harmonic_eq_classical_on_ball_two hr
    (hg.continuousOn.mono hsub) (classical_harmonic_isViscosityHarmonicTwo hgsmall)
    (p := fun _ => g x) continuousOn_const (InnerProductSpace.harmonicOnNhd_const (g x))
    (by
      intro y hy
      exact hradial y (hsub (sphere_subset_closedBall hy)) x hx (mem_sphere.mp hy))
  exact (hEq (mem_closedBall.mpr (by simpa only [dist_self] using hr.le))).symm

end PowerConvexity
