import PowerConvexity.Calculus.CompactParaboloidContactsTwo

/-! # Small value error gives an actual compact interior contact set.
The same actual minima give vertex coverage and the volume lower bound.
The smallness assumption is a value bound, not a derivative bound.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
local notation "E" => DeGiorgi.AmbientSpace (2+2)

theorem small_value_lower_contacts_inside_three_quarter_ball_two
    {w : E → ℝ} {a R : ℝ} {x0 : E} (ha : 0 < a) (hR : 0 < R)
    (hsmall : ∀ x ∈ closedBall x0 R, |w x| ≤ a*R^2/128) :
    lowerParaboloidContactsTwo a w (closedBall x0 R) (closedBall x0 (R/2)) ⊆
      ball x0 (3*R/4) := by
  rintro x ⟨hx,c,hc,hm⟩
  have hcD : c ∈ closedBall x0 R :=
    closedBall_subset_closedBall (by linarith : R/2 ≤ R) hc
  have hcmp := hm hcD
  simp only [mem_setOf_eq,translatedBallPotential,quadraticBallPotential,sub_self,norm_zero,
    zero_pow (by norm_num : (2 : ℕ) ≠ 0),sub_zero,mul_zero,add_zero] at hcmp
  have hxl := (abs_le.mp (hsmall x hx)).1
  have hcu := (abs_le.mp (hsmall c hcD)).2
  have hsq : ‖x-c‖^2 ≤ R^2/32 := by
    exact le_of_mul_le_mul_left (by nlinarith only [hcmp,hxl,hcu]) ha
  have hn : ‖x-c‖ < R/4 := by
    apply (sq_lt_sq₀ (norm_nonneg (x-c)) (by positivity : 0 ≤ R/4)).mp
    nlinarith only [hsq,sq_pos_of_pos hR]
  have hcn : ‖c-x0‖ ≤ R/2 := by simpa only [mem_closedBall,dist_eq_norm] using hc
  rw [mem_ball,dist_eq_norm]
  calc
    ‖x-x0‖ = ‖(x-c)+(c-x0)‖ := by congr 1; module
    _ ≤ ‖x-c‖+‖c-x0‖ := norm_add_le _ _
    _ < 3*R/4 := by linarith only [hn,hcn]

theorem lowerParaboloidContactsTwo_actual_quadratic_lower_bound
    {a : ℝ} {w : E → ℝ} {D V : Set E}
    (hinterior : lowerParaboloidContactsTwo a w D V ⊆ interior D)
    (hreg : ∀ x ∈ lowerParaboloidContactsTwo a w D V, ContDiffAt ℝ 2 w x) :
    ∀ x ∈ lowerParaboloidContactsTwo a w D V, ∀ v : E,
      -(a*‖v‖^2) ≤ realHessian w x v v := by
  intro x hx v
  have hkeep := hx
  obtain ⟨_hx,c,_hc,hm⟩ := hkeep
  have hl := hm.isLocalMin (mem_interior_iff_mem_nhds.mp (hinterior hx))
  have hq := (translatedBallPotential_contDiff (a/2) 0 c 2).contDiffAt (x := x)
  have hh := realHessian_nonneg_of_isLocalMin ((hreg x hx).add hq) hl v
  rw [realHessian_add (hreg x hx) hq] at hh
  change 0 ≤ realHessian w x v v+realHessian (translatedBallPotential (a/2) 0 c) x v v at hh
  rw [translatedBallPotential_realHessian,real_inner_self_eq_norm_sq] at hh
  linarith only [hh]

theorem exists_universal_small_value_contact_volume_bound_two :
    ∃ K : ℝ, 0 < K ∧ ∀ (w : E → ℝ) (x0 : E) (a R : ℝ),
      0 < a → a ≤ 1 → 0 < R →
      ContinuousOn w (closedBall x0 R) → ContDiffOn ℝ 2 w (ball x0 R) →
      (∀ x ∈ ball x0 R, (1+complexHessian realDirections imagDirections w x).det = 1) →
      (∀ x ∈ closedBall x0 R, |w x| ≤ a*R^2/128) →
      let S := lowerParaboloidContactsTwo a w (closedBall x0 R) (closedBall x0 (R/2))
      IsCompact S ∧ S ⊆ ball x0 (3*R/4) ∧
        volume (closedBall x0 (R/2)) ≤ ENNReal.ofReal K*volume S := by
  obtain ⟨K,hK,hmeasure⟩ := exists_universal_small_lower_contact_image_measure_bound_two
  refine ⟨K,hK,?_⟩
  intro w x0 a R ha ha1 hR hwc hw hdet hsmall
  let S := lowerParaboloidContactsTwo a w (closedBall x0 R) (closedBall x0 (R/2))
  have hS : IsCompact S := lowerParaboloidContactsTwo_isCompact
    (isCompact_closedBall x0 R) (isCompact_closedBall x0 (R/2)) hwc
  have hSsmall : S ⊆ ball x0 (3*R/4) :=
    small_value_lower_contacts_inside_three_quarter_ball_two ha hR hsmall
  have hSR : S ⊆ ball x0 R := hSsmall.trans (ball_subset_ball (by linarith))
  have hSI : S ⊆ interior (closedBall x0 R) := hSR.trans ball_subset_interior_closedBall
  have hreg (x : E) (hx : x ∈ S) : ContDiffAt ℝ 2 w x :=
    hw.contDiffAt (isOpen_ball.mem_nhds (hSR hx))
  have hcover := lowerParaboloidContactsTwo_vertex_coverage ha.ne'
    (isCompact_closedBall x0 R) ⟨x0,mem_closedBall_self hR.le⟩ hwc hSI
    (fun x hx => (hreg x hx).differentiableAt (by norm_num))
  have hvol := hmeasure w S a hS.measurableSet ha ha1 hreg
    (fun x hx => hdet x (hSR hx))
    (lowerParaboloidContactsTwo_actual_quadratic_lower_bound hSI hreg)
  exact ⟨hS,hSsmall,(measure_mono hcover).trans hvol⟩

end PowerConvexity
