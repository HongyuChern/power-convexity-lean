import PowerConvexity.Calculus.SmallContactMeasureDecayTwo
import PowerConvexity.Calculus.SmallContactSeedAndLevelsTwo

/-! # Actual superlevel-set decay from the same solution's contacts.
The initial contact is attained, and each contacted point has its
actual function value below the corresponding opening.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff Topology ENNReal
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
local notation "E" => DeGiorgi.AmbientSpace (2+2)

theorem exists_universal_small_value_superlevel_decay_two :
    ∃ M θ : ℝ, 2 ≤ M ∧ 0 < θ ∧ θ < 1 ∧ ∀ (w : E → ℝ),
      ContinuousOn w (closedBall 0 1) → ContDiffOn ℝ 2 w (interior (closedBall 0 1)) →
      (∀ x ∈ interior (closedBall 0 1),
        (1+complexHessian realDirections imagDirections w x).det = 1) →
      (∀ x ∈ closedBall 0 1, 0 ≤ w x) →
      ∀ a : ℝ, 0 < a → w 0 ≤ a/1024 →
      ∀ k : ℕ, M^k*a ≤ 1 →
      volume.real {x | x ∈ closedBall (0 : E) (1/8) ∧ M^k*a < w x} ≤
        θ^k*volume.real (closedBall (0 : E) (1/8)) := by
  obtain ⟨M,θ,hM,hθ,hθ1,hdecay⟩ := exists_universal_contact_measure_geometric_decay_two
  refine ⟨M,θ,hM,hθ,hθ1,?_⟩
  intro w hwc hw hdet hnon a ha hzero k hsmall
  have hseed := nonnegative_small_value_has_inner_contact_two hwc hnon ha hzero
  obtain ⟨_hkn,hkm⟩ := hdecay w hwc hw hdet a ha hseed k hsmall
  have hMp : 0 < M := by linarith only [hM]
  have hMone : 1 ≤ M := by linarith only [hM]
  have hb : 0 < M^k*a := mul_pos (pow_pos hMp _) ha
  have hab : a ≤ M^k*a := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (one_le_pow₀ hMone) ha.le
  have hzeroB : w 0 ≤ (M^k*a)/2 := by linarith only [hzero,hab,ha]
  have hsub : {x | x ∈ closedBall (0 : E) (1/8) ∧ M^k*a < w x} ⊆
      closedBall 0 (1/8) \ innerLowerParaboloidContactsTwo (M^k*a) w := by
    intro x hx
    refine ⟨hx.1,?_⟩
    intro hcontact
    exact (not_lt_of_ge (lower_unit_contact_value_le_opening_two hb.le hzeroB hcontact.1)) hx.2
  have hU : volume (closedBall (0 : E) (1/8)) ≠ (⊤ : ℝ≥0∞) :=
    (isCompact_closedBall _ _).measure_lt_top.ne
  exact (measureReal_mono hsub (measure_ne_top_of_subset sdiff_subset hU)).trans hkm

end PowerConvexity
