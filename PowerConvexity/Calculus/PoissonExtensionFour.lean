import PowerConvexity.Calculus.PoissonBoundaryLimitFour

/-! # Actual continuous harmonic extension and viscosity regularity on a ball.
The extension is the explicit Poisson integral in the interior and the
specified datum on the actual sphere. Regularity of a viscosity solution
then follows from the already proved comparison with this actual function.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology
namespace PowerConvexity
local notation "E" => DeGiorgi.AmbientSpace (2+2)
local notation "S" => sphere (0 : E) 1

def unitPoissonExtensionFour (f : S → ℝ) (x : E) : ℝ := by
  classical
  exact if hx : x ∈ sphere (0 : E) 1 then f ⟨x,hx⟩
  else poissonIntegralFour unitSphereProbabilityFour f x

theorem unitPoissonExtensionFour_on_sphere (f : S → ℝ) (ξ : S) :
    unitPoissonExtensionFour f ξ = f ξ := by
  simp [unitPoissonExtensionFour,ξ.property]

theorem unitPoissonExtensionFour_on_ball (f : S → ℝ) {x : E} (hx : x ∈ ball 0 1) :
    unitPoissonExtensionFour f x = poissonIntegralFour unitSphereProbabilityFour f x := by
  have hs : x ∉ sphere (0 : E) 1 := fun h => (Set.disjoint_left.mp sphere_disjoint_ball h hx).elim
  simp only [unitPoissonExtensionFour,dif_neg hs]

theorem unitPoissonExtensionFour_C2 {f : S → ℝ} (hf : Continuous f) :
    ContDiffOn ℝ 2 (unitPoissonExtensionFour f) (ball 0 1) := by
  apply (poissonIntegralFour_C2_and_hessian unitSphereProbabilityFour hf).1.congr
  intro x hx
  exact unitPoissonExtensionFour_on_ball f hx

theorem unitPoissonExtensionFour_harmonic {f : S → ℝ} (hf : Continuous f) :
    InnerProductSpace.HarmonicOnNhd (unitPoissonExtensionFour f) (ball 0 1) := by
  intro x hx
  have heq : unitPoissonExtensionFour f =ᶠ[𝓝 x]
      poissonIntegralFour unitSphereProbabilityFour f := by
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    exact unitPoissonExtensionFour_on_ball f hy
  exact (InnerProductSpace.harmonicAt_congr_nhds heq).mpr
    (poissonIntegralFour_harmonic_on_unit_ball unitSphereProbabilityFour hf x hx)

theorem unitPoissonExtensionFour_continuousOn_closedBall {f : S → ℝ} (hf : Continuous f) :
    ContinuousOn (unitPoissonExtensionFour f) (closedBall 0 1) := by
  have hS : ContinuousOn (unitPoissonExtensionFour f) (sphere (0 : E) 1) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    change Continuous (fun ξ : S => unitPoissonExtensionFour f ξ)
    simpa only [unitPoissonExtensionFour_on_sphere] using hf
  intro x hx
  have hx' : x ∈ ball (0 : E) 1 ∪ sphere (0 : E) 1 := by
    simpa only [ball_union_sphere] using hx
  rcases hx' with hb|hs
  · exact ((unitPoissonExtensionFour_C2 hf).contDiffAt (isOpen_ball.mem_nhds hb)).continuousAt.continuousWithinAt
  · let a : S := ⟨x,hs⟩
    have hball : ContinuousWithinAt (unitPoissonExtensionFour f) (ball 0 1) x := by
      change Tendsto (unitPoissonExtensionFour f) (𝓝[ball (0 : E) 1] x)
        (𝓝 (unitPoissonExtensionFour f x))
      rw [show unitPoissonExtensionFour f x = f a from unitPoissonExtensionFour_on_sphere f a]
      have heq : poissonIntegralFour unitSphereProbabilityFour f =ᶠ[𝓝[ball (0 : E) 1] x]
          unitPoissonExtensionFour f := by
        filter_upwards [self_mem_nhdsWithin] with y hy
        exact (unitPoissonExtensionFour_on_ball f hy).symm
      exact (poissonIntegralFour_tendsto_unitSphere hf a).congr' heq
    simpa only [ball_union_sphere] using hball.union (hS x hs)

theorem exists_classical_harmonic_unitBall_extension_four {f : S → ℝ} (hf : Continuous f) :
    ∃ p : E → ℝ, ContinuousOn p (closedBall 0 1) ∧ ContDiffOn ℝ 2 p (ball 0 1) ∧
      InnerProductSpace.HarmonicOnNhd p (ball 0 1) ∧ ∀ ξ : S, p ξ = f ξ :=
  ⟨unitPoissonExtensionFour f,unitPoissonExtensionFour_continuousOn_closedBall hf,
    unitPoissonExtensionFour_C2 hf,unitPoissonExtensionFour_harmonic hf,
    unitPoissonExtensionFour_on_sphere f⟩

theorem viscosity_harmonic_C2_on_unitBall_two {g : E → ℝ}
    (hgc : ContinuousOn g (closedBall 0 1)) (hg : IsViscosityHarmonicTwo g (ball 0 1)) :
    ContDiffOn ℝ 2 g (ball 0 1) := by
  let f : S → ℝ := fun ξ => g ξ
  have hf : Continuous f := continuousOn_iff_continuous_domRestrict.mp
    (hgc.mono sphere_subset_closedBall)
  let p := unitPoissonExtensionFour f
  have heq := viscosity_harmonic_eq_classical_on_ball_two (by norm_num : (0:ℝ) < 1)
    hgc hg (unitPoissonExtensionFour_continuousOn_closedBall hf) (unitPoissonExtensionFour_harmonic hf)
    (by intro x hx; exact (unitPoissonExtensionFour_on_sphere f ⟨x,hx⟩).symm)
  apply (unitPoissonExtensionFour_C2 hf).congr
  intro x hx
  exact heq (ball_subset_closedBall hx)

theorem viscosity_harmonic_classical_on_unitBall_two {g : E → ℝ}
    (hgc : ContinuousOn g (closedBall 0 1)) (hg : IsViscosityHarmonicTwo g (ball 0 1)) :
    InnerProductSpace.HarmonicOnNhd g (ball 0 1) :=
  hg.classical_harmonic_of_C2 isOpen_ball (viscosity_harmonic_C2_on_unitBall_two hgc hg)

end PowerConvexity
