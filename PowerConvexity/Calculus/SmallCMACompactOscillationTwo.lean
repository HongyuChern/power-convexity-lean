import PowerConvexity.Calculus.SmallCMAOscillationRescaledTwo
import CHS.Analysis.CompactOscillation

/-! # Contraction of the actual compact oscillation.
The zero-oscillation case is included; no positivity of the actual
oscillation is added to the public estimate.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Set Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)

theorem exists_universal_small_CMA_compact_oscillation_contraction_two :
    ∃ τ : ℝ, 0 < τ ∧ τ < 1 ∧ ∀ (w : E → ℝ) (c : E) (r : ℝ),
      0 < r → ContinuousOn w (closedBall c r) → ContDiffOn ℝ 2 w (ball c r) →
      (∀ x ∈ ball c r, (1+complexHessian realDirections imagDirections w x).PosSemidef) →
      (∀ x ∈ ball c r, (1+complexHessian realDirections imagDirections w x).det = 1) →
      compactOsc w (closedBall c r) ≤ r^2 →
      compactOsc w (closedBall c (r/32)) ≤ τ*compactOsc w (closedBall c r) := by
  obtain ⟨κ,hκ,hκ1,hstep⟩ := exists_universal_small_CMA_rescaled_oscillation_two
  refine ⟨1-κ,by linarith only [hκ1],by linarith only [hκ],?_⟩
  intro w c r hr hwc hw hpsh hdet hsmall
  have hK : IsCompact (closedBall c r) := isCompact_closedBall _ _
  have hKn : (closedBall c r).Nonempty := ⟨c,mem_closedBall_self hr.le⟩
  have hL : IsCompact (closedBall c (r/32)) := isCompact_closedBall _ _
  have hLn : (closedBall c (r/32)).Nonempty := ⟨c,mem_closedBall_self (by positivity)⟩
  have hsub : closedBall c (r/32) ⊆ closedBall c r :=
    closedBall_subset_closedBall (by linarith only [hr])
  have hnon := compactOsc_nonneg hK hKn hwc
  by_cases heq : compactOsc w (closedBall c r) = 0
  · have hh := compactOsc_mono hK hLn hwc hsub
    simpa only [heq,mul_zero] using hh
  have hpos : 0 < compactOsc w (closedBall c r) := lt_of_le_of_ne hnon (Ne.symm heq)
  have hbound : ∀ x ∈ closedBall c r,
      compactInf w (closedBall c r) ≤ w x ∧
        w x ≤ compactInf w (closedBall c r)+compactOsc w (closedBall c r) := by
    intro x hx
    refine ⟨compactInf_le hK hwc hx,?_⟩
    have hh := le_compactSup hK hwc hx
    dsimp only [compactOsc]
    linarith only [hh]
  apply compactOsc_le_of_sub_le hL hLn (hwc.mono hsub)
  exact hstep w c r (compactInf w (closedBall c r)) (compactOsc w (closedBall c r))
    hr hpos hsmall hwc hw hpsh hdet hbound

end PowerConvexity
