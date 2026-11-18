import PowerConvexity.Analysis.ActualWeakSmoothHarmonicTwo

/-! # Actual weak representatives on physical balls.
Affine transport preserves the actual almost-everywhere equivalence and
the original weak equation on the full ball. Regularity holds on its
concentric half ball, with no pre-existing continuous representative input.
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

theorem ballNormalizationFour_quasiMeasurePreserving {R : ℝ} (hR : 0 < R) (c : F) :
    Measure.QuasiMeasurePreserving (ballNormalizationFour c R) volume volume := by
  have hs := Measure.quasiMeasurePreserving_smul (μ := (volume : Measure F))
    (r := R⁻¹) (inv_ne_zero hR.ne')
  have ht := (measurePreserving_add_right (volume : Measure F) (-c)).quasiMeasurePreserving
  change Measure.QuasiMeasurePreserving (fun x : F => R⁻¹ • (x-c)) volume volume
  simpa only [Function.comp_def,sub_eq_add_neg] using hs.comp ht

theorem actual_homogeneous_weak_ball_continuous_representative_two
    {c : F} {R : ℝ} (hR : 0 < R) (A : NormalizedEllipticCoeff (2+2) (ball c R))
    {u : F → ℝ} (hu : IsHomogeneousWeakSolution A.1 u) :
    ∃ v : F → ℝ, v =ᵐ[volume.restrict (ball c R)] u ∧
      IsHomogeneousWeakSolution A.1 v ∧ ContinuousOn v (ball c (R/2)) := by
  let AR := rescaleNormalizedCoeffToUnitBall hR A
  have hur : IsHomogeneousWeakSolution AR.1 (rescaleToUnitBall (x₀ := c) (R := R) u) :=
    rescaleToUnitBall_isHomogeneousWeakSolution hR A.1 hu
  obtain ⟨v,hvu,_,hvc,_⟩ := actual_homogeneous_weak_continuous_representative
    (by norm_num : 2 < ((2+2 : ℕ) : ℝ)) AR hur
  let V : F → ℝ := fun x => v (ballNormalizationFour c R x)
  have hmaps : MapsTo (ballNormalizationFour c R) (ball c R) (ball (0 : F) 1) :=
    fun x hx => (ballNormalizationFour_mem_ball_iff hR c x).mpr hx
  have hae : V =ᵐ[volume.restrict (ball c R)] u := by
    have hh := ((ballNormalizationFour_quasiMeasurePreserving hR c).restrict hmaps).ae hvu
    filter_upwards [hh] with x hx
    change v (ballNormalizationFour c R x) = u x
    simpa only [rescaleToUnitBall,ballNormalizationFour_inverse hR.ne'] using hx
  refine ⟨V,hae,actual_homogeneousWeakSolution_congr_ae hae.symm hu,?_⟩
  apply hvc.comp (ballNormalizationFour_contDiff c R 0).continuous.continuousOn
  intro x hx
  rw [mem_ball,dist_zero_right,ballNormalizationFour_norm hR]
  apply (div_lt_iff₀ hR).mpr
  have hx' := mem_ball.mp hx
  linarith

theorem actual_identity_weak_ball_smooth_representative_two
    {c : F} {R : ℝ} (hR : 0 < R) {u : F → ℝ}
    (hu : IsHomogeneousWeakSolution (identityNormalizedEllipticCoeffTwo (ball c R)).1 u) :
    ∃ v : F → ℝ, v =ᵐ[volume.restrict (ball c R)] u ∧
      IsHomogeneousWeakSolution (identityNormalizedEllipticCoeffTwo (ball c R)).1 v ∧
      InnerProductSpace.HarmonicOnNhd v (ball c (R/2)) ∧
      ∀ n : ℕ∞ω, ContDiffOn ℝ n v (ball c (R/2)) := by
  obtain ⟨v,hvu,hv,hvc⟩ := actual_homogeneous_weak_ball_continuous_representative_two
    hR (identityNormalizedEllipticCoeffTwo (ball c R)) hu
  have hs := (isHomogeneousWeakSolution_isSolution hv).restrict_ball isOpen_ball
    (half_pos hR) (closedBall_subset_ball (by linarith : R/2 < R))
  have hw : IsHomogeneousWeakSolution (identityNormalizedEllipticCoeffTwo (ball c (R/2))).1 v :=
    IsSolution.isHomogeneousWeakSolution isOpen_ball hs
  have hh := actual_identity_weak_continuous_is_classical_two isOpen_ball hw hvc
  exact ⟨v,hvu,hv,hh,fun n => actual_classical_harmonic_contDiffOn_two isOpen_ball hh n⟩

end PowerConvexity
