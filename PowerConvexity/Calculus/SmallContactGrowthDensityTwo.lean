import PowerConvexity.Calculus.SmallContactGrowthTwo
import PowerConvexity.Analysis.ContactGrowthGeometryTwo

/-! # A fixed-volume proportion of genuine larger-opening contacts.
All constants precede the function, domain, contact and ball. The set on
the right is the original function's actual global contact set.
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

theorem exists_universal_small_contact_growth_density_two :
    ∃ M C : ℝ, 2 ≤ M ∧ 0 < C ∧
      ∀ (w : E → ℝ) (D : Set E) (x0 y1 x1 : E) (a r : ℝ),
        IsCompact D → Convex ℝ D →
        ContinuousOn w D → ContDiffOn ℝ 2 w (interior D) →
        (∀ x ∈ interior D,
          (1+complexHessian realDirections imagDirections w x).det = 1) →
        0 < a → M*a ≤ 1 → 0 < r →
        closedBall x0 r ⊆ interior D → y1 ∈ D → x1 ∈ ball x0 r →
        IsMinOn (fun x => w x+translatedBallPotential (a/2) 0 y1 x) D x1 →
        volume (closedBall x0 r) ≤ ENNReal.ofReal C*
          volume (lowerParaboloidContactsTwo (M*a) w D D ∩ closedBall x0 (r/8)) := by
  obtain ⟨M,K,hM,hK,hgrowth⟩ := exists_universal_small_contact_growth_two
  refine ⟨M,(128 : ℝ)^4*K,hM,by positivity,?_⟩
  intro w D x0 y1 x1 a r hD hconv hwc hw hdet ha hMa hr hball hy1 hx1 hm
  obtain ⟨z,_hz,S,_hS,hSball,hScontact,hvol⟩ :=
    hgrowth w D x0 y1 x1 a r hD hconv hwc hw hdet ha hMa hr hball hy1 hx1 hm
  have hvertex := weighted_contact_vertices_contain_small_ball_two hM hr y1 z
  have hsmall : volume (closedBall (M⁻¹ • (y1+(M-1) • z)) (r/128)) ≤
      ENNReal.ofReal K*volume S := (measure_mono hvertex).trans hvol
  have hsubset : S ⊆ lowerParaboloidContactsTwo (M*a) w D D ∩ closedBall x0 (r/8) :=
    fun _ hx => ⟨hScontact hx,ball_subset_closedBall (hSball hx)⟩
  calc
    volume (closedBall x0 r) = ENNReal.ofReal ((128 : ℝ)^4)*
        volume (closedBall (M⁻¹ • (y1+(M-1) • z)) (r/128)) :=
      closedBall_radius_div_128_volume_two _ _ _
    _ ≤ ENNReal.ofReal ((128 : ℝ)^4)*(ENNReal.ofReal K*volume S) :=
      mul_le_mul_of_nonneg_left hsmall zero_le
    _ ≤ ENNReal.ofReal ((128 : ℝ)^4)*(ENNReal.ofReal K*
        volume (lowerParaboloidContactsTwo (M*a) w D D ∩ closedBall x0 (r/8))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (measure_mono hsubset) zero_le) zero_le
    _ = ENNReal.ofReal ((128 : ℝ)^4*K)*
        volume (lowerParaboloidContactsTwo (M*a) w D D ∩ closedBall x0 (r/8)) := by
      rw [ENNReal.ofReal_mul (by positivity),mul_assoc]

end PowerConvexity
