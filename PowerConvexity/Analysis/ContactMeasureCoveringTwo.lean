import PowerConvexity.Calculus.SmallValueContactMeasureTwo
import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.Topology.Bases

/-! # Summing local contact-growth estimates over a genuine Vitali family.
Only the explicit local volume inequality is assumed here. The actual
contact-set application supplies it separately. The disjoint family is
countable by its nonempty interiors; all measure identities are checked.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal Topology
namespace PowerConvexity
local notation "E" => DeGiorgi.AmbientSpace (2+2)

theorem contact_measure_vitali_growth_two
    {U F G : Set E} {r : E → ℝ} {C R : ℝ}
    (hmeas : MeasurableSet (G \ F))
    (hpos : ∀ x ∈ U \ F, 0 < r x)
    (hbound : ∀ x ∈ U \ F, r x ≤ R)
    (hgrowth : ∀ x ∈ U \ F,
      volume (closedBall x (4*r x)) ≤
        ENNReal.ofReal C*volume ((G \ F) ∩ closedBall x (r x))) :
    volume (U \ F) ≤ ENNReal.ofReal C*volume (G \ F) := by
  obtain ⟨s,hsub,hdis,hcover⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall
    (U \ F) (fun x : E => x) r R hbound 4 (by norm_num)
  have hcount : s.Countable := hdis.countable_of_nonempty_interior (by
    intro x hx
    exact ⟨x,ball_subset_interior_closedBall (mem_ball_self (hpos x (hsub hx)))⟩)
  letI : Countable s := hcount.to_subtype
  have hcovered : U \ F ⊆ ⋃ i : s, closedBall (i : E) (4*r i) := by
    intro x hx
    obtain ⟨y,hy,hin⟩ := hcover x hx
    exact mem_iUnion.mpr ⟨⟨y,hy⟩,hin (mem_closedBall_self (hpos x hx).le)⟩
  have hpieces : Pairwise (fun i j : s => Disjoint
      ((G \ F) ∩ closedBall (i : E) (r i)) ((G \ F) ∩ closedBall (j : E) (r j))) := by
    intro i j hij
    exact (hdis i.2 j.2 (fun he => hij (Subtype.ext he))).mono inter_subset_right inter_subset_right
  have hpm (i : s) : MeasurableSet ((G \ F) ∩ closedBall (i : E) (r i)) :=
    hmeas.inter measurableSet_closedBall
  calc
    volume (U \ F) ≤ volume (⋃ i : s, closedBall (i : E) (4*r i)) := measure_mono hcovered
    _ ≤ ∑' i : s, volume (closedBall (i : E) (4*r i)) := measure_iUnion_le _
    _ ≤ ∑' i : s, ENNReal.ofReal C*volume ((G \ F) ∩ closedBall (i : E) (r i)) :=
      ENNReal.tsum_le_tsum (fun i => hgrowth i (hsub i.2))
    _ = ENNReal.ofReal C*(∑' i : s, volume ((G \ F) ∩ closedBall (i : E) (r i))) := by
      rw [ENNReal.tsum_mul_left]
    _ = ENNReal.ofReal C*volume (⋃ i : s, (G \ F) ∩ closedBall (i : E) (r i)) := by
      rw [measure_iUnion hpieces hpm]
    _ ≤ ENNReal.ofReal C*volume (G \ F) :=
      mul_le_mul_of_nonneg_left (measure_mono (iUnion_subset (fun _ => inter_subset_left))) zero_le

end PowerConvexity
