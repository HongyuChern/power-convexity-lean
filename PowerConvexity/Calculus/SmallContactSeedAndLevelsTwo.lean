import PowerConvexity.Calculus.SmallContactDistanceGrowthTwo

/-! # A genuine initial contact and actual contact-value bounds.
The seed is constructed by compact minimum attainment. The value bound
uses the same unit domain and actual vertex, without a derivative proxy.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open Set Metric
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
local notation "E" => DeGiorgi.AmbientSpace (2+2)

theorem nonnegative_small_value_has_inner_contact_two
    {w : E → ℝ} (hw : ContinuousOn w (closedBall 0 1))
    (hnon : ∀ x ∈ closedBall 0 1, 0 ≤ w x)
    {a : ℝ} (ha : 0 < a) (hzero : w 0 ≤ a/1024) :
    (innerLowerParaboloidContactsTwo a w).Nonempty := by
  have hz : (0 : E) ∈ closedBall 0 1 := mem_closedBall_self zero_le_one
  obtain ⟨x,hx,hm⟩ := (isCompact_closedBall (0 : E) 1).exists_isMinOn ⟨0,hz⟩
    (hw.add (translatedBallPotential_contDiff (a/2) 0 (0 : E) 0).continuous.continuousOn)
  have hcmp : w x+(a/2)*‖x‖^2 ≤ w 0 := by
    simpa only [mem_setOf_eq,Pi.add_apply,translatedBallPotential,quadraticBallPotential,
      sub_zero,norm_zero,zero_pow (by norm_num : (2 : ℕ) ≠ 0),mul_zero,add_zero] using hm hz
  have hpen : a*‖x‖^2 ≤ a/512 := by nlinarith only [hcmp,hnon x hx,hzero]
  have hsq : ‖x‖^2 ≤ (1:ℝ)/512 :=
    le_of_mul_le_mul_left (by nlinarith only [hpen]) ha
  have hnorm : ‖x‖ ≤ (1:ℝ)/8 :=
    (sq_le_sq₀ (norm_nonneg x) (by norm_num : (0:ℝ) ≤ 1/8)).mp (by nlinarith only [hsq])
  exact ⟨x,⟨hx,0,hz,hm⟩,by simpa only [mem_closedBall,dist_zero_right] using hnorm⟩

theorem lower_unit_contact_value_le_reference_two
    {w : E → ℝ} {a : ℝ} (ha : 0 ≤ a) {x : E}
    (hx : x ∈ lowerParaboloidContactsTwo a w (closedBall 0 1) (closedBall 0 1)) :
    w x ≤ w 0+a/2 := by
  obtain ⟨_hxD,y,hy,hm⟩ := hx
  have hyn : ‖y‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using hy
  have hysq : ‖y‖^2 ≤ 1 := by nlinarith only [(sq_le_sq₀ (norm_nonneg y) zero_le_one).mpr hyn]
  have hcmp : w x+translatedBallPotential (a/2) 0 y x ≤ w 0+(a/2)*‖y‖^2 := by
    simpa only [mem_setOf_eq,Pi.add_apply,translatedBallPotential,quadraticBallPotential,
      zero_sub,norm_neg,zero_pow (by norm_num : (2 : ℕ) ≠ 0),sub_zero] using
      hm (mem_closedBall_self zero_le_one)
  have hq : 0 ≤ translatedBallPotential (a/2) 0 y x := by
    unfold translatedBallPotential quadraticBallPotential
    simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0),sub_zero]
    positivity
  have hmul := mul_le_mul_of_nonneg_left hysq (by positivity : 0 ≤ a/2)
  linarith only [hcmp,hq,hmul]

theorem lower_unit_contact_value_le_opening_two
    {w : E → ℝ} {a : ℝ} (ha : 0 ≤ a) (hzero : w 0 ≤ a/2) {x : E}
    (hx : x ∈ lowerParaboloidContactsTwo a w (closedBall 0 1) (closedBall 0 1)) :
    w x ≤ a := by
  have hh := lower_unit_contact_value_le_reference_two ha hx
  linarith only [hh,hzero]

end PowerConvexity
