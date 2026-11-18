import PowerConvexity.Calculus.ContactOpeningLocalizationTwo

/-! # Genuine lower-contact sets are monotone in the opening.
The new vertex is the actual convex combination of the previous vertex
and the contact point. Global minimality on the same domain is preserved.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open Set
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
local notation "E" => DeGiorgi.AmbientSpace (2+2)

theorem lowerParaboloidContactsTwo_mono_opening
    {D : Set E} (hD : Convex ℝ D) (w : E → ℝ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    lowerParaboloidContactsTwo a w D D ⊆ lowerParaboloidContactsTwo b w D D := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  let c : ℝ := b-a
  have hc : 0 ≤ c := sub_nonneg.mpr hab
  have hac : a+c = b := by dsimp only [c]; ring
  rintro x ⟨hx,y,hy,hm⟩
  let Y : E := b⁻¹ • (a • y+c • x)
  have hrel : (a+c) • Y = a • y+c • x := by
    rw [hac]
    dsimp only [Y]
    rw [smul_smul,mul_inv_cancel₀ hb.ne',one_smul]
  have hsum : a/b+c/b = 1 := by rw [← add_div,hac]; exact div_self hb.ne'
  have hYD : Y ∈ D := by
    have hh := hD hy hx (div_nonneg ha.le hb.le) (div_nonneg hc hb.le) hsum
    convert hh using 1 <;> dsimp only [Y] <;> simp only [div_eq_mul_inv] <;> module
  refine ⟨hx,Y,hYD,?_⟩
  intro z hz
  have hmz : w x+translatedBallPotential (a/2) 0 y x ≤
      w z+translatedBallPotential (a/2) 0 y z := hm hz
  have hq : translatedBallPotential (c/2) 0 x x ≤ translatedBallPotential (c/2) 0 x z := by
    simp only [translatedBallPotential,quadraticBallPotential,sub_self,norm_zero,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0),sub_zero,mul_zero]
    positivity
  have hxi := translated_paraboloid_sum_difference_two a c y x Y x hrel
  have hzi := translated_paraboloid_sum_difference_two a c y x Y z hrel
  rw [hac] at hxi hzi
  change w x+translatedBallPotential (b/2) 0 Y x ≤ w z+translatedBallPotential (b/2) 0 Y z
  linarith only [hmz,hq,hxi,hzi]

end PowerConvexity
