import PowerConvexity.Calculus.ViscosityHarmonicBallRegularityTwo

/-! # Actual Poisson representation for the original harmonic function.
Boundary data are its actual trace on the selected sphere. The representation
therefore applies to the same compactness limit, not to a replacement with
unspecified boundary values.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
local notation "E" => DeGiorgi.AmbientSpace (2+2)
local notation "S" => sphere (0 : E) 1

theorem continuous_actual_ball_boundary_data_four {g : E → ℝ} {c : E} {R : ℝ}
    (hR : 0 < R) (hgc : ContinuousOn g (closedBall c R)) :
    Continuous (fun ξ : S => g (c+R • (ξ : E))) := by
  apply continuousOn_univ.mp
  have hcmap : Continuous (fun ξ : S => c+R • (ξ : E)) := by fun_prop
  apply hgc.comp hcmap.continuousOn
  intro ξ _
  have hn : ‖(ξ : E)‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using ξ.property
  simp [mem_closedBall,dist_eq_norm,norm_smul,abs_of_pos hR,hn]

theorem viscosity_harmonic_actual_poisson_representation_four {g : E → ℝ} {c : E} {R : ℝ}
    (hR : 0 < R) (hgc : ContinuousOn g (closedBall c R))
    (hg : IsViscosityHarmonicTwo g (ball c R)) {x : E} (hx : x ∈ ball c R) :
    g x = poissonIntegralFour unitSphereProbabilityFour
      (fun ξ : S => g (c+R • (ξ : E))) (ballNormalizationFour c R x) := by
  let f : S → ℝ := fun ξ => g (c+R • (ξ : E))
  have hf := continuous_actual_ball_boundary_data_four hR hgc
  let p : E → ℝ := fun x => unitPoissonExtensionFour f (ballNormalizationFour c R x)
  have hpH : InnerProductSpace.HarmonicOnNhd p (ball c R) :=
    classical_harmonic_ball_normalization_two (unitPoissonExtensionFour_harmonic hf) hR c
  have hpC : ContinuousOn p (closedBall c R) :=
    (unitPoissonExtensionFour_continuousOn_closedBall hf).comp
      (ballNormalizationFour_contDiff c R 0).continuous.continuousOn
      (fun y hy => (ballNormalizationFour_mem_closedBall_iff hR c y).mpr hy)
  have hb (y : E) (hy : y ∈ sphere c R) : g y = p y := by
    let ξ : S := ⟨ballNormalizationFour c R y,(ballNormalizationFour_mem_sphere_iff hR c y).mpr hy⟩
    have he := unitPoissonExtensionFour_on_sphere f ξ
    change p y = g (c+R • ballNormalizationFour c R y) at he
    rw [ballNormalizationFour_inverse hR.ne'] at he
    exact he.symm
  have heq := viscosity_harmonic_eq_classical_on_ball_two hR hgc hg hpC hpH hb
  exact (heq (ball_subset_closedBall hx)).trans
    (unitPoissonExtensionFour_on_ball f ((ballNormalizationFour_mem_ball_iff hR c x).mpr hx))

theorem classical_harmonic_actual_poisson_representation_four {g : E → ℝ} {c : E} {R : ℝ}
    (hR : 0 < R) (hgc : ContinuousOn g (closedBall c R))
    (hg : InnerProductSpace.HarmonicOnNhd g (ball c R)) {x : E} (hx : x ∈ ball c R) :
    g x = poissonIntegralFour unitSphereProbabilityFour
      (fun ξ : S => g (c+R • (ξ : E))) (ballNormalizationFour c R x) :=
  viscosity_harmonic_actual_poisson_representation_four hR hgc
    (classical_harmonic_isViscosityHarmonicTwo hg) hx

theorem classical_harmonic_unitBall_actual_poisson_representation_four {g : E → ℝ}
    (hgc : ContinuousOn g (closedBall 0 1))
    (hg : InnerProductSpace.HarmonicOnNhd g (ball 0 1)) :
    EqOn g (poissonIntegralFour unitSphereProbabilityFour (fun ξ : S => g ξ)) (ball 0 1) := by
  intro x hx
  simpa [ballNormalizationFour] using
    classical_harmonic_actual_poisson_representation_four (by norm_num : (0:ℝ)<1) hgc hg hx

end PowerConvexity
