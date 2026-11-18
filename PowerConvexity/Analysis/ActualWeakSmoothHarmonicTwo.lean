import PowerConvexity.Calculus.PoissonIntegralSmoothFour
import PowerConvexity.Calculus.HarmonicPoissonRepresentationFour
import PowerConvexity.Analysis.ActualWeakClassicalHarmonicTwo

/-! # All interior derivative orders of actual weak harmonic representatives.
The Poisson boundary trace is the trace of the same classical representative.
No regularity of an unspecified replacement is substituted for the original
weak solution. All derivative orders follow from the actual kernel integral.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "F" => AmbientSpace (2+2)
local notation "S" => sphere (0 : F) 1

theorem classical_harmonic_contDiff_on_ball_four {g : F → ℝ} {c : F} {R : ℝ}
    (hR : 0 < R) (hc : ContinuousOn g (closedBall c R))
    (hg : InnerProductSpace.HarmonicOnNhd g (ball c R)) (n : ℕ∞ω) :
    ContDiffOn ℝ n g (ball c R) := by
  let f : S → ℝ := fun xi => g (c+R • (xi : F))
  have hf : Continuous f := continuous_actual_ball_boundary_data_four hR hc
  intro x hx
  have hp := (poissonIntegralFour_contDiffAt unitSphereProbabilityFour hf
    ((ballNormalizationFour_mem_ball_iff hR c x).mpr hx) n).comp x
      (ballNormalizationFour_contDiff c R n).contDiffAt
  have he : g =ᶠ[𝓝 x] (fun y => poissonIntegralFour unitSphereProbabilityFour f
      (ballNormalizationFour c R y)) := by
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    exact classical_harmonic_actual_poisson_representation_four hR hc hg hy
  exact (hp.congr_of_eventuallyEq he).contDiffWithinAt

theorem actual_classical_harmonic_contDiffOn_two {g : F → ℝ} {U : Set F}
    (hU : IsOpen U) (hg : InnerProductSpace.HarmonicOnNhd g U) (n : ℕ∞ω) :
    ContDiffOn ℝ n g U := by
  intro x hx
  obtain ⟨r,hr,hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  have hK : closedBall x (r/2) ⊆ U := by
    intro y hy
    exact hrU (mem_ball.mpr ((mem_closedBall.mp hy).trans_lt (by linarith)))
  have hB : ball x (r/2) ⊆ U := fun y hy => hK (ball_subset_closedBall hy)
  have hc := classical_harmonic_contDiff_on_ball_four (half_pos hr)
    (hg.contDiffOn.continuousOn.mono hK) (fun y hy => hg y (hB hy)) n
  exact (hc.contDiffAt (isOpen_ball.mem_nhds (mem_ball_self (half_pos hr)))).contDiffWithinAt

theorem actual_identity_weak_smooth_representative_two {u : F → ℝ}
    (hu : IsHomogeneousWeakSolution (identityNormalizedEllipticCoeffTwo (ball (0 : F) 1)).1 u) :
    ∃ v : F → ℝ, v =ᵐ[volume.restrict (ball (0 : F) 1)] u ∧
      IsHomogeneousWeakSolution (identityNormalizedEllipticCoeffTwo (ball (0 : F) 1)).1 v ∧
      InnerProductSpace.HarmonicOnNhd v (ball (0 : F) (1/2 : ℝ)) ∧
      ∀ n : ℕ∞ω, ContDiffOn ℝ n v (ball (0 : F) (1/2 : ℝ)) := by
  obtain ⟨v,hvu,hv,hh,_⟩ := actual_identity_weak_classical_representative_two hu
  exact ⟨v,hvu,hv,hh,fun n => actual_classical_harmonic_contDiffOn_two isOpen_ball hh n⟩

theorem actual_smooth_harmonic_replacement_two {u : F → ℝ}
    (hu : MemW1p 2 u (ball (0 : F) 1)) :
    ∃ v : F → ℝ,
      IsHomogeneousWeakSolution (identityNormalizedEllipticCoeffTwo (ball (0 : F) 1)).1 v ∧
      MemH01 (fun x => v x-u x) (ball (0 : F) 1) ∧
      (∀ n : ℕ∞ω, ContDiffOn ℝ n v (ball (0 : F) (1/2 : ℝ))) ∧
      ∀ w : F → ℝ,
        IsHomogeneousWeakSolution (identityNormalizedEllipticCoeffTwo (ball (0 : F) 1)).1 w →
        MemH01 (fun x => w x-u x) (ball (0 : F) 1) →
        ContinuousOn w (ball (0 : F) (1/2 : ℝ)) →
        EqOn v w (ball (0 : F) (1/2 : ℝ)) := by
  obtain ⟨v,hv,hzero,hh,huniq⟩ := actual_classical_harmonic_replacement_two hu
  exact ⟨v,hv,hzero,fun n => actual_classical_harmonic_contDiffOn_two isOpen_ball hh n,huniq⟩

end PowerConvexity
