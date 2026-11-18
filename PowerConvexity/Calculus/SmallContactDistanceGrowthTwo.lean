import PowerConvexity.Calculus.SmallContactGrowthDensityTwo
import PowerConvexity.Analysis.ContactCoveringBallsTwo

/-! # Actual local growth at the distance to the old contact set.
The fixed inner set is closed B_(1/8). All comparison balls are proved
to stay inside the unit ball. The new portion excludes the old contacts.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff Topology ENNReal
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
local notation "E" => DeGiorgi.AmbientSpace (2+2)

def innerLowerParaboloidContactsTwo (a : ℝ) (w : E → ℝ) : Set E :=
  lowerParaboloidContactsTwo a w (closedBall 0 1) (closedBall 0 1) ∩ closedBall 0 (1/8)

theorem exists_universal_contact_distance_growth_two :
    ∃ M C : ℝ, 2 ≤ M ∧ 0 < C ∧ ∀ (w : E → ℝ),
      ContinuousOn w (closedBall 0 1) → ContDiffOn ℝ 2 w (interior (closedBall 0 1)) →
      (∀ x ∈ interior (closedBall 0 1),
        (1+complexHessian realDirections imagDirections w x).det = 1) →
      ∀ a : ℝ, 0 < a → M*a ≤ 1 → (innerLowerParaboloidContactsTwo a w).Nonempty →
      IsCompact (innerLowerParaboloidContactsTwo a w) ∧
      IsCompact (innerLowerParaboloidContactsTwo (M*a) w) ∧
      innerLowerParaboloidContactsTwo a w ⊆ innerLowerParaboloidContactsTwo (M*a) w ∧
      ∀ x ∈ closedBall 0 (1/8) \ innerLowerParaboloidContactsTwo a w,
        let r := infDist x (innerLowerParaboloidContactsTwo a w)
        0 < r ∧ r ≤ 1/4 ∧ volume (closedBall x (2*r)) ≤
          ENNReal.ofReal C*volume ((innerLowerParaboloidContactsTwo (M*a) w \
            innerLowerParaboloidContactsTwo a w) ∩ closedBall x (r/2)) := by
  obtain ⟨M,C,hM,hC,hgrowth⟩ := exists_universal_small_contact_growth_density_two
  refine ⟨M,C,hM,hC,?_⟩
  intro w hwc hw hdet a ha hMa hFn
  let F := innerLowerParaboloidContactsTwo a w
  let G := innerLowerParaboloidContactsTwo (M*a) w
  have hF : IsCompact F :=
    (lowerParaboloidContactsTwo_isCompact (isCompact_closedBall 0 1) (isCompact_closedBall 0 1) hwc).inter_right isClosed_closedBall
  have hG : IsCompact G :=
    (lowerParaboloidContactsTwo_isCompact (isCompact_closedBall 0 1) (isCompact_closedBall 0 1) hwc).inter_right isClosed_closedBall
  have hFsub : F ⊆ closedBall 0 (1/8) := fun _ hx => hx.2
  have haM : a ≤ M*a := by
    have hh := mul_le_mul_of_nonneg_right hM ha.le
    linarith only [hh,ha]
  have hFG : F ⊆ G := fun _ hx =>
    ⟨lowerParaboloidContactsTwo_mono_opening (convex_closedBall 0 1) w ha haM hx.1,hx.2⟩
  refine ⟨hF,hG,hFG,?_⟩
  intro x hx
  let r := infDist x F
  obtain ⟨hr,hrle,c,hbig,⟨y,hyball,hyF⟩,hsmall,hdis⟩ :=
    contact_cover_shift_at_distance_two hF hFn hFsub hx.1 hx.2
  obtain ⟨_hyD,y1,hy1,hmin⟩ := hyF.1
  have hvol := hgrowth w (closedBall 0 1) c y1 y a (2*r)
    (isCompact_closedBall 0 1) (convex_closedBall 0 1) hwc hw hdet ha hMa
    (by dsimp only [r]; positivity)
    (hbig.trans ball_subset_interior_closedBall) hy1 hyball hmin
  have he : (2*r)/8 = r/4 := by ring
  rw [he] at hvol
  have hsubset : lowerParaboloidContactsTwo (M*a) w (closedBall 0 1) (closedBall 0 1) ∩
      closedBall c (r/4) ⊆ (G \ F) ∩ closedBall x (r/2) := by
    intro p hp
    have hh := hsmall hp.2
    exact ⟨⟨⟨hp.1,hh.1⟩,fun hpF => Set.disjoint_left.mp hdis hh.2 hpF⟩,hh.2⟩
  refine ⟨hr,hrle,?_⟩
  calc
    volume (closedBall x (2*r)) = volume (closedBall c (2*r)) := by
      rw [Measure.addHaar_closedBall_center volume x,Measure.addHaar_closedBall_center volume c]
    _ ≤ ENNReal.ofReal C*volume
        (lowerParaboloidContactsTwo (M*a) w (closedBall 0 1) (closedBall 0 1) ∩ closedBall c (r/4)) := hvol
    _ ≤ ENNReal.ofReal C*volume ((G \ F) ∩ closedBall x (r/2)) :=
      mul_le_mul_of_nonneg_left (measure_mono hsubset) zero_le

end PowerConvexity
