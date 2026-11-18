import PowerConvexity.Calculus.SmallContactSuperlevelDecayTwo

/-! # Actual contacts and superlevel decay from an off-center small value.
The reference point may be anywhere in the same inner ball of radius 1/32.
Both the initial contact and every contact value are proved for the
original function on the original unit domain.
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

theorem nonnegative_off_center_small_value_has_inner_contact_two
    {w : E → ℝ} (hw : ContinuousOn w (closedBall 0 1))
    (hnon : ∀ x ∈ closedBall 0 1, 0 ≤ w x)
    {a : ℝ} (ha : 0 < a) {z : E} (hz : z ∈ closedBall 0 (1/32 : ℝ))
    (hsmall : w z ≤ a/1024) :
    (innerLowerParaboloidContactsTwo a w).Nonempty := by
  have hzD : z ∈ closedBall (0 : E) 1 :=
    (closedBall_subset_closedBall (by norm_num : (1/32 : ℝ) ≤ 1)) hz
  obtain ⟨x,hx,hm⟩ := (isCompact_closedBall (0 : E) 1).exists_isMinOn ⟨z,hzD⟩
    (hw.add (translatedBallPotential_contDiff (a/2) 0 z 0).continuous.continuousOn)
  have hcmp : w x+(a/2)*‖x-z‖^2 ≤ w z := by
    simpa only [mem_setOf_eq,Pi.add_apply,translatedBallPotential,quadraticBallPotential,
      sub_self,norm_zero,zero_pow (by norm_num : (2 : ℕ) ≠ 0),mul_zero,add_zero,sub_zero] using hm hzD
  have hpen : a*‖x-z‖^2 ≤ a/512 := by nlinarith only [hcmp,hnon x hx,hsmall]
  have hsq : ‖x-z‖^2 ≤ (1:ℝ)/512 :=
    le_of_mul_le_mul_left (by nlinarith only [hpen]) ha
  have hnear : ‖x-z‖ ≤ (1:ℝ)/16 :=
    (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1/16)).mp (by nlinarith only [hsq])
  have hzn : ‖z‖ ≤ (1:ℝ)/32 := by simpa only [mem_closedBall,dist_zero_right] using hz
  have hxn : ‖x‖ ≤ (1:ℝ)/8 := by
    have ht := norm_add_le (x-z) z
    rw [sub_add_cancel] at ht
    linarith only [ht,hnear,hzn]
  exact ⟨x,⟨hx,z,hzD,hm⟩,by simpa only [mem_closedBall,dist_zero_right] using hxn⟩

theorem lower_unit_contact_value_le_at_two
    {w : E → ℝ} {a : ℝ} (ha : 0 ≤ a) {z x : E} (hz : z ∈ closedBall 0 1)
    (hx : x ∈ lowerParaboloidContactsTwo a w (closedBall 0 1) (closedBall 0 1)) :
    w x ≤ w z+2*a := by
  obtain ⟨_hxD,y,hy,hm⟩ := hx
  have hzn : ‖z‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using hz
  have hyn : ‖y‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using hy
  have hdist : ‖z-y‖ ≤ 2 := (norm_sub_le z y).trans (by linarith only [hzn,hyn])
  have hsq : ‖z-y‖^2 ≤ 4 := by
    nlinarith only [(sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 2)).mpr hdist]
  have hcmp : w x+(a/2)*‖x-y‖^2 ≤ w z+(a/2)*‖z-y‖^2 := by
    simpa only [mem_setOf_eq,Pi.add_apply,translatedBallPotential,quadraticBallPotential,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0),sub_zero] using hm hz
  have hleft : 0 ≤ (a/2)*‖x-y‖^2 := by positivity
  have hright := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ a/2)
  linarith only [hcmp,hleft,hright]

theorem exists_universal_off_center_superlevel_decay_two :
    ∃ M θ : ℝ, 2 ≤ M ∧ 0 < θ ∧ θ < 1 ∧ ∀ (w : E → ℝ),
      ContinuousOn w (closedBall 0 1) → ContDiffOn ℝ 2 w (interior (closedBall 0 1)) →
      (∀ x ∈ interior (closedBall 0 1),
        (1+complexHessian realDirections imagDirections w x).det = 1) →
      (∀ x ∈ closedBall 0 1, 0 ≤ w x) →
      ∀ a : ℝ, 0 < a → ∀ z ∈ closedBall (0 : E) (1/32 : ℝ), w z ≤ a/1024 →
      ∀ k : ℕ, M^k*a ≤ 1 →
      volume.real {x | x ∈ closedBall (0 : E) (1/8) ∧ 3*(M^k*a) < w x} ≤
        θ^k*volume.real (closedBall (0 : E) (1/8)) := by
  obtain ⟨M,θ,hM,hθ,hθ1,hdecay⟩ := exists_universal_contact_measure_geometric_decay_two
  refine ⟨M,θ,hM,hθ,hθ1,?_⟩
  intro w hwc hw hdet hnon a ha z hz hsmall k hbound
  have hseed := nonnegative_off_center_small_value_has_inner_contact_two hwc hnon ha hz hsmall
  obtain ⟨_hkn,hkm⟩ := hdecay w hwc hw hdet a ha hseed k hbound
  have hMp : 0 < M := by linarith only [hM]
  have hMone : 1 ≤ M := by linarith only [hM]
  have hb : 0 < M^k*a := mul_pos (pow_pos hMp _) ha
  have hab : a ≤ M^k*a := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (one_le_pow₀ hMone) ha.le
  have hzD : z ∈ closedBall (0 : E) 1 :=
    (closedBall_subset_closedBall (by norm_num : (1/32 : ℝ) ≤ 1)) hz
  have hsub : {x | x ∈ closedBall (0 : E) (1/8) ∧ 3*(M^k*a) < w x} ⊆
      closedBall 0 (1/8) \ innerLowerParaboloidContactsTwo (M^k*a) w := by
    intro x hx
    refine ⟨hx.1,?_⟩
    intro hcontact
    have hv := lower_unit_contact_value_le_at_two hb.le hzD hcontact.1
    linarith only [hv,hsmall,hab,ha,hx.2]
  have hU : volume (closedBall (0 : E) (1/8)) ≠ (⊤ : ℝ≥0∞) :=
    (isCompact_closedBall _ _).measure_lt_top.ne
  exact (measureReal_mono hsub (measure_ne_top_of_subset sdiff_subset hU)).trans hkm

end PowerConvexity
