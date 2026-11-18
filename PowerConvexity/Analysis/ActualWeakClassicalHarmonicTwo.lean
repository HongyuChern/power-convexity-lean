import PowerConvexity.Analysis.ActualWeakViscosityHarmonicTwo
import PowerConvexity.Analysis.ActualWeakHarmonicRepresentative

/-! # Actual classical harmonic representatives from the original weak equation.
The representative is constructed by Moser regularity, proved to satisfy
the local viscosity tests, and identified with actual Poisson solutions.
Interior classical regularity is a conclusion, not a premise.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "F" => AmbientSpace (2+2)

theorem actual_identity_weak_continuous_is_classical_two
    {U : Set F} (hU : IsOpen U) {u : F → ℝ}
    (hu : IsHomogeneousWeakSolution (identityNormalizedEllipticCoeffTwo U).1 u)
    (hc : ContinuousOn u U) : InnerProductSpace.HarmonicOnNhd u U :=
  (actual_identity_weak_isViscosityHarmonic_two hU hu hc).classical_harmonic_two hU

theorem actual_identity_weak_classical_representative_two
    {u : F → ℝ}
    (hu : IsHomogeneousWeakSolution (identityNormalizedEllipticCoeffTwo (ball (0 : F) 1)).1 u) :
    ∃ v : F → ℝ, v =ᵐ[volume.restrict (ball (0 : F) 1)] u ∧
      IsHomogeneousWeakSolution (identityNormalizedEllipticCoeffTwo (ball (0 : F) 1)).1 v ∧
      InnerProductSpace.HarmonicOnNhd v (ball (0 : F) (1/2 : ℝ)) ∧
      ContDiffOn ℝ 2 v (ball (0 : F) (1/2 : ℝ)) := by
  obtain ⟨v,hvu,hv,hvc,_⟩ := actual_homogeneous_weak_continuous_representative
    (by norm_num : 2 < ((2+2 : ℕ) : ℝ)) (identityNormalizedEllipticCoeffTwo (ball (0 : F) 1)) hu
  have hs := (isHomogeneousWeakSolution_isSolution hv).restrict_ball isOpen_ball
    (by norm_num : 0 < (1/2 : ℝ)) (closedBall_subset_ball (by norm_num : (1/2 : ℝ) < 1))
  have hh : IsHomogeneousWeakSolution
      (identityNormalizedEllipticCoeffTwo (ball (0 : F) (1/2 : ℝ))).1 v :=
    IsSolution.isHomogeneousWeakSolution isOpen_ball hs
  have hc := actual_identity_weak_continuous_is_classical_two isOpen_ball hh hvc
  exact ⟨v,hvu,hv,hc,hc.contDiffOn⟩

theorem actual_classical_harmonic_replacement_two
    {u : F → ℝ} (hu : MemW1p 2 u (ball (0 : F) 1)) :
    ∃ v : F → ℝ,
      IsHomogeneousWeakSolution (identityNormalizedEllipticCoeffTwo (ball (0 : F) 1)).1 v ∧
      MemH01 (fun x => v x-u x) (ball (0 : F) 1) ∧
      InnerProductSpace.HarmonicOnNhd v (ball (0 : F) (1/2 : ℝ)) ∧
      ∀ w : F → ℝ,
        IsHomogeneousWeakSolution (identityNormalizedEllipticCoeffTwo (ball (0 : F) 1)).1 w →
        MemH01 (fun x => w x-u x) (ball (0 : F) 1) →
        ContinuousOn w (ball (0 : F) (1/2 : ℝ)) →
        EqOn v w (ball (0 : F) (1/2 : ℝ)) := by
  obtain ⟨v,hv,hzero,hvc,huniq⟩ := actual_continuous_harmonic_replacement
    (by norm_num : 2 < ((2+2 : ℕ) : ℝ)) (identityNormalizedEllipticCoeffTwo (ball (0 : F) 1)) hu
  have hs := (isHomogeneousWeakSolution_isSolution hv).restrict_ball isOpen_ball
    (by norm_num : 0 < (1/2 : ℝ)) (closedBall_subset_ball (by norm_num : (1/2 : ℝ) < 1))
  have hh : IsHomogeneousWeakSolution
      (identityNormalizedEllipticCoeffTwo (ball (0 : F) (1/2 : ℝ))).1 v :=
    IsSolution.isHomogeneousWeakSolution isOpen_ball hs
  exact ⟨v,hv,hzero,actual_identity_weak_continuous_is_classical_two isOpen_ball hh hvc,huniq⟩

end PowerConvexity
