import PowerConvexity.Calculus.SmallContactDistanceGrowthTwo
import PowerConvexity.Analysis.ContactMeasureCoveringTwo

/-! # Actual global growth of the inner contact sets.
The local inequality is supplied by the same determinant-one solution;
the covering radius is half its actual distance to the old contact set.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff Topology ENNReal
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
local notation "E" => DeGiorgi.AmbientSpace (2+2)

theorem exists_universal_contact_global_growth_two :
    ∃ M C : ℝ, 2 ≤ M ∧ 0 < C ∧ ∀ (w : E → ℝ),
      ContinuousOn w (closedBall 0 1) → ContDiffOn ℝ 2 w (interior (closedBall 0 1)) →
      (∀ x ∈ interior (closedBall 0 1),
        (1+complexHessian realDirections imagDirections w x).det = 1) →
      ∀ a : ℝ, 0 < a → M*a ≤ 1 → (innerLowerParaboloidContactsTwo a w).Nonempty →
      IsCompact (innerLowerParaboloidContactsTwo a w) ∧
      IsCompact (innerLowerParaboloidContactsTwo (M*a) w) ∧
      innerLowerParaboloidContactsTwo a w ⊆ innerLowerParaboloidContactsTwo (M*a) w ∧
      volume (closedBall 0 (1/8) \ innerLowerParaboloidContactsTwo a w) ≤
        ENNReal.ofReal C*volume (innerLowerParaboloidContactsTwo (M*a) w \
          innerLowerParaboloidContactsTwo a w) := by
  obtain ⟨M,C,hM,hC,hgrowth⟩ := exists_universal_contact_distance_growth_two
  refine ⟨M,C,hM,hC,?_⟩
  intro w hwc hw hdet a ha hMa hFn
  obtain ⟨hF,hG,hFG,hlocal⟩ := hgrowth w hwc hw hdet a ha hMa hFn
  refine ⟨hF,hG,hFG,?_⟩
  let F := innerLowerParaboloidContactsTwo a w
  let G := innerLowerParaboloidContactsTwo (M*a) w
  let r : E → ℝ := fun x => infDist x F/2
  apply contact_measure_vitali_growth_two (r := r) (R := 1/8)
    (hG.measurableSet.diff hF.measurableSet)
  · intro x hx
    exact half_pos (hlocal x hx).1
  · intro x hx
    have hh := (hlocal x hx).2.1
    dsimp only [r]
    linarith only [hh]
  · intro x hx
    dsimp only [r]
    rw [show 4*(infDist x F/2) = 2*infDist x F by ring]
    exact (hlocal x hx).2.2

end PowerConvexity
