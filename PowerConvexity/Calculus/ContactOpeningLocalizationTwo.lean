import PowerConvexity.Calculus.SmallValueContactMeasureTwo

/-! # Localizing actual contacts after increasing their opening.
The input is one controlled value of a nonnegative function on the same
compact domain. The quadratic identity then recovers contacts of the
original function, with the actual weighted vertices.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open Set Metric Filter InnerProductSpace
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
local notation "E" => DeGiorgi.AmbientSpace (2+2)

theorem lower_contacts_of_one_small_value_localized_two
    {v : E → ℝ} {D : Set E} {z : E} {a r C : ℝ}
    (ha : 0 < a) (hr : 0 < r) (hC : 0 ≤ C) (hz : z ∈ D)
    (hv : ∀ x ∈ D, 0 ≤ v x) (hvz : v z ≤ C*a*r^2) :
    lowerParaboloidContactsTwo (8192*(C+1)*a) v D (closedBall z (r/64)) ⊆
      ball z (r/16) := by
  rintro x ⟨hx,y,hy,hm⟩
  have hA : 0 < 8192*(C+1)*a := by positivity
  have hyz : ‖y-z‖ ≤ r/64 := by simpa only [mem_closedBall,dist_eq_norm] using hy
  have hzy : ‖z-y‖^2 ≤ r^2/4096 := by
    rw [norm_sub_rev]
    have hh := (sq_le_sq₀ (norm_nonneg (y-z)) (by positivity : 0 ≤ r/64)).mpr hyz
    nlinarith only [hh]
  have hcmp : v x+(8192*(C+1)*a/2)*‖x-y‖^2 ≤
      v z+(8192*(C+1)*a/2)*‖z-y‖^2 := by
    simpa only [mem_setOf_eq,translatedBallPotential,quadraticBallPotential,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0),sub_zero] using hm hz
  have hqz := mul_le_mul_of_nonneg_left hzy (le_of_lt (half_pos hA))
  have hxupper : (8192*(C+1)*a/2)*‖x-y‖^2 ≤
      (2*C+1)*a*r^2 := by
    nlinarith only [hcmp,hqz,hvz,hv x hx]
  have hxy : ‖x-y‖ < r/32 := by
    by_contra hh
    have hs : (r/32)^2 ≤ ‖x-y‖^2 :=
      (sq_le_sq₀ (by positivity : 0 ≤ r/32) (norm_nonneg _)).mpr (le_of_not_gt hh)
    have hp := mul_le_mul_of_nonneg_left hs (le_of_lt (half_pos hA))
    have hstrict : 0 < (2*C+3)*a*r^2 := by positivity
    nlinarith only [hxupper,hp,hstrict]
  rw [mem_ball,dist_eq_norm]
  calc
    ‖x-z‖ = ‖(x-y)+(y-z)‖ := by congr 1; module
    _ ≤ ‖x-y‖+‖y-z‖ := norm_add_le _ _
    _ < r/16 := by linarith only [hxy,hyz,hr]

theorem translated_paraboloid_sum_difference_two
    (a b : ℝ) (y1 y Y x : E)
    (hY : (a+b) • Y = a • y1+b • y) :
    translatedBallPotential (a/2) 0 y1 x+translatedBallPotential (b/2) 0 y x-
        translatedBallPotential ((a+b)/2) 0 Y x =
      translatedBallPotential (a/2) 0 y1 0+translatedBallPotential (b/2) 0 y 0-
        translatedBallPotential ((a+b)/2) 0 Y 0 := by
  have hi := congrArg (fun p : E => inner ℝ x p) hY
  simp only [inner_smul_right,inner_add_right] at hi
  simp only [translatedBallPotential,quadraticBallPotential,
    zero_pow (by norm_num : (2 : ℕ) ≠ 0),sub_zero,zero_sub,norm_neg,
    norm_sub_sq_real]
  nlinarith only [hi]

theorem lowerParaboloidContactsTwo_combine_openings
    (a b m : ℝ) (w : E → ℝ) (y1 : E) (D V : Set E) (Y : E → E)
    (hY : ∀ y ∈ V, (a+b) • Y y = a • y1+b • y) :
    lowerParaboloidContactsTwo b
        (fun x => w x+translatedBallPotential (a/2) 0 y1 x-m) D V ⊆
      lowerParaboloidContactsTwo (a+b) w D (Y '' V) := by
  rintro x ⟨hx,y,hy,hm⟩
  refine ⟨hx,Y y,⟨y,hy,rfl⟩,?_⟩
  intro z hz
  have hh : (w x+translatedBallPotential (a/2) 0 y1 x-m)+
      translatedBallPotential (b/2) 0 y x ≤
      (w z+translatedBallPotential (a/2) 0 y1 z-m)+
      translatedBallPotential (b/2) 0 y z := hm hz
  have hxid := translated_paraboloid_sum_difference_two a b y1 y (Y y) x (hY y hy)
  have hzid := translated_paraboloid_sum_difference_two a b y1 y (Y y) z (hY y hy)
  change w x+translatedBallPotential ((a+b)/2) 0 (Y y) x ≤
    w z+translatedBallPotential ((a+b)/2) 0 (Y y) z
  linarith only [hh,hxid,hzid]

end PowerConvexity
