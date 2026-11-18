import PowerConvexity.Calculus.ViscosityHarmonicStrictComparisonTwo

/-! # Actual comparison on balls without a strict Laplace inequality.
The strict barrier is an explicit zero-boundary quadratic on the same
ball. Its coefficient is removed without assuming regularity of the
viscosity function beyond its actual continuity.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section
open Set Filter Metric Matrix
open scoped ContDiff Topology BigOperators
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
local notation "E" => DeGiorgi.AmbientSpace (2+2)

theorem actual_C2_block_trace_add_ball_potential_two
    {p : E → ℝ} {x : E} (hp : ContDiffAt ℝ 2 p x) (a R : ℝ) (c : E) :
    (realBlockHessian realDirections imagDirections
      (fun y => p y+translatedBallPotential a R c y) x).trace =
      (realBlockHessian realDirections imagDirections p x).trace+8*a := by
  have he : (fun y => p y+translatedBallPotential a R c y) =
      (fun y => (p y+translatedBallPotential a 0 c y)+(-a*R^2)) := by
    funext y
    simp only [translatedBallPotential,quadraticBallPotential,zero_pow (by decide : 2 ≠ 0),sub_zero]
    ring
  rw [he]
  have hh : realBlockHessian realDirections imagDirections
      (fun y => (p y+translatedBallPotential a 0 c y)+(-a*R^2)) x =
      realBlockHessian realDirections imagDirections
        (fun y => p y+translatedBallPotential a 0 c y) x := by
    ext i j
    simp only [realBlockHessian,CHS.Calculus.realHessian_add_const]
  rw [hh,actual_C2_block_trace_add_translated_ball_two hp]

theorem viscosity_harmonic_le_classical_superharmonic_on_ball_two
    {g p : E → ℝ} {c : E} {R : ℝ} (hR : 0 < R)
    (hgc : ContinuousOn g (closedBall c R)) (hg : IsViscosityHarmonicTwo g (ball c R))
    (hpc : ContinuousOn p (closedBall c R)) (hp : ContDiffOn ℝ 2 p (ball c R))
    (htrace : ∀ x ∈ ball c R, (realBlockHessian realDirections imagDirections p x).trace ≤ 0)
    (hboundary : ∀ x ∈ sphere c R, g x ≤ p x) :
    ∀ x ∈ closedBall c R, g x ≤ p x := by
  intro x hx
  by_contra hbad
  have hgap : 0 < g x-p x := sub_pos.mpr (lt_of_not_ge hbad)
  let δ : ℝ := (g x-p x)/(2*(R^2+1))
  have hden : 0 < 2*(R^2+1) := by positivity
  have hδ : 0 < δ := div_pos hgap hden
  have hδeq : δ*(2*(R^2+1)) = g x-p x := div_mul_cancel₀ _ hden.ne'
  let P : E → ℝ := fun y => p y+translatedBallPotential (-δ) R c y
  have hPc : ContinuousOn P (closedBall c R) := hpc.add
    (translatedBallPotential_contDiff (-δ) R c 2).continuous.continuousOn
  have hP : ContDiffOn ℝ 2 P (ball c R) := hp.add
    (translatedBallPotential_contDiff (-δ) R c 2).contDiffOn
  have hPt (y : E) (hy : y ∈ ball c R) :
      (realBlockHessian realDirections imagDirections P y).trace < 0 := by
    rw [show P = fun z => p z+translatedBallPotential (-δ) R c z by rfl,
      actual_C2_block_trace_add_ball_potential_two (hp.contDiffAt (isOpen_ball.mem_nhds hy))]
    linarith only [htrace y hy,hδ]
  have hPb (y : E) (hy : y ∈ frontier (ball c R)) : g y ≤ P y := by
    have hys : y ∈ sphere c R := by simpa only [frontier_ball c hR.ne'] using hy
    have hnorm : ‖y-c‖ = R := by simpa only [mem_sphere,dist_eq_norm] using hys
    change g y ≤ p y+translatedBallPotential (-δ) R c y
    rw [translatedBallPotential_zero_on_sphere (-δ) R c y hnorm,add_zero]
    exact hboundary y hys
  have hh := viscosity_harmonic_le_strict_classical_superharmonic_two isOpen_ball
    (by rw [closure_ball c hR.ne']; exact isCompact_closedBall c R)
    (by simpa only [closure_ball c hR.ne'] using hgc) hg
    (by simpa only [closure_ball c hR.ne'] using hPc) hP hPt hPb x
    (by simpa only [closure_ball c hR.ne'] using hx)
  have hnon : 0 ≤ δ*‖x-c‖^2 := mul_nonneg hδ.le (sq_nonneg _)
  dsimp only [P,translatedBallPotential,quadraticBallPotential] at hh
  nlinarith only [hh,hδeq,hnon,hδ]

theorem classical_subharmonic_le_viscosity_harmonic_on_ball_two
    {g p : E → ℝ} {c : E} {R : ℝ} (hR : 0 < R)
    (hgc : ContinuousOn g (closedBall c R)) (hg : IsViscosityHarmonicTwo g (ball c R))
    (hpc : ContinuousOn p (closedBall c R)) (hp : ContDiffOn ℝ 2 p (ball c R))
    (htrace : ∀ x ∈ ball c R, 0 ≤ (realBlockHessian realDirections imagDirections p x).trace)
    (hboundary : ∀ x ∈ sphere c R, p x ≤ g x) :
    ∀ x ∈ closedBall c R, p x ≤ g x := by
  intro x hx
  by_contra hbad
  have hgap : 0 < p x-g x := sub_pos.mpr (lt_of_not_ge hbad)
  let δ : ℝ := (p x-g x)/(2*(R^2+1))
  have hden : 0 < 2*(R^2+1) := by positivity
  have hδ : 0 < δ := div_pos hgap hden
  have hδeq : δ*(2*(R^2+1)) = p x-g x := div_mul_cancel₀ _ hden.ne'
  let P : E → ℝ := fun y => p y+translatedBallPotential δ R c y
  have hPc : ContinuousOn P (closedBall c R) := hpc.add
    (translatedBallPotential_contDiff δ R c 2).continuous.continuousOn
  have hP : ContDiffOn ℝ 2 P (ball c R) := hp.add
    (translatedBallPotential_contDiff δ R c 2).contDiffOn
  have hPt (y : E) (hy : y ∈ ball c R) :
      0 < (realBlockHessian realDirections imagDirections P y).trace := by
    rw [show P = fun z => p z+translatedBallPotential δ R c z by rfl,
      actual_C2_block_trace_add_ball_potential_two (hp.contDiffAt (isOpen_ball.mem_nhds hy))]
    linarith only [htrace y hy,hδ]
  have hPb (y : E) (hy : y ∈ frontier (ball c R)) : P y ≤ g y := by
    have hys : y ∈ sphere c R := by simpa only [frontier_ball c hR.ne'] using hy
    have hnorm : ‖y-c‖ = R := by simpa only [mem_sphere,dist_eq_norm] using hys
    change p y+translatedBallPotential δ R c y ≤ g y
    rw [translatedBallPotential_zero_on_sphere δ R c y hnorm,add_zero]
    exact hboundary y hys
  have hh := strict_classical_subharmonic_le_viscosity_harmonic_two isOpen_ball
    (by rw [closure_ball c hR.ne']; exact isCompact_closedBall c R)
    (by simpa only [closure_ball c hR.ne'] using hgc) hg
    (by simpa only [closure_ball c hR.ne'] using hPc) hP hPt hPb x
    (by simpa only [closure_ball c hR.ne'] using hx)
  have hnon : 0 ≤ δ*‖x-c‖^2 := mul_nonneg hδ.le (sq_nonneg _)
  dsimp only [P,translatedBallPotential,quadraticBallPotential] at hh
  nlinarith only [hh,hδeq,hnon,hδ]

end PowerConvexity
