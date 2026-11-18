import PowerConvexity.Calculus.SmallCMAOscillationTwo
import PowerConvexity.Calculus.CMADeviationRescaleTwo

/-! # Actual oscillation improvement in arbitrary ball coordinates.
The quadratic smallness threshold is checked before normalization.
No transformed regularity, equation, or branch is assumed separately.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff Topology BigOperators ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)

theorem exists_universal_small_CMA_rescaled_oscillation_two :
    ∃ κ : ℝ, 0 < κ ∧ κ < 1 ∧ ∀ (w : E → ℝ) (c : E) (r m ε : ℝ),
      0 < r → 0 < ε → ε ≤ r^2 →
      ContinuousOn w (closedBall c r) → ContDiffOn ℝ 2 w (ball c r) →
      (∀ x ∈ ball c r, (1+complexHessian realDirections imagDirections w x).PosSemidef) →
      (∀ x ∈ ball c r, (1+complexHessian realDirections imagDirections w x).det = 1) →
      (∀ x ∈ closedBall c r, m ≤ w x ∧ w x ≤ m+ε) →
      ∀ x ∈ closedBall c (r/32), ∀ y ∈ closedBall c (r/32),
        w x-w y ≤ (1-κ)*ε := by
  obtain ⟨κ,hκ,hκ1,hstep⟩ := exists_universal_small_CMA_oscillation_improvement_two
  refine ⟨κ,hκ,hκ1,?_⟩
  intro w c r m ε hr hε hsmall hwc hw hpsh hdet hbound
  let v := normalizedCMADeviationTwo c r m w
  let T : E → E := fun z => c+r • z
  have hr2 : 0 < r^2 := sq_pos_of_pos hr
  have hi : 0 < (r^2)⁻¹ := inv_pos.mpr hr2
  have hT : Continuous T := by dsimp only [T]; fun_prop
  have hmapcl : MapsTo T (closedBall 0 1) (closedBall c r) := by
    intro z hz
    have hn : ‖z‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using hz
    change dist (c+r • z) c ≤ r
    rw [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_of_nonneg hr.le]
    nlinarith only [mul_le_mul_of_nonneg_left hn hr.le]
  have hmap : MapsTo T (ball 0 1) (ball c r) := by
    intro z hz
    have hn : ‖z‖ < 1 := by simpa only [mem_ball,dist_zero_right] using hz
    change dist (c+r • z) c < r
    rw [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_of_nonneg hr.le]
    nlinarith only [mul_lt_mul_of_pos_left hn hr]
  have hvc : ContinuousOn v (closedBall 0 1) :=
    continuousOn_const.mul ((hwc.comp hT.continuousOn hmapcl).sub continuousOn_const)
  have hv : ContDiffOn ℝ 2 v (interior (closedBall 0 1)) := by
    rw [interior_closedBall' (0 : E) 1]
    intro z hz
    exact (normalizedCMADeviationTwo_contDiffAt (hw.contDiffAt (isOpen_ball.mem_nhds (hmap hz)))).contDiffWithinAt
  have hH (z : E) (hz : z ∈ interior (closedBall (0 : E) 1)) :
      complexHessian realDirections imagDirections v z =
        complexHessian realDirections imagDirections w (T z) := by
    have hzB : z ∈ ball (0 : E) 1 := by simpa only [interior_closedBall' (0 : E) 1] using hz
    exact normalizedCMADeviationTwo_complexHessian hr.ne'
      (hw.contDiffAt (isOpen_ball.mem_nhds (hmap hzB)))
  have hvpsh : ∀ z ∈ interior (closedBall (0 : E) 1),
      (1+complexHessian realDirections imagDirections v z).PosSemidef := by
    intro z hz
    rw [hH z hz]
    exact hpsh (T z) (hmap (by simpa only [interior_closedBall' (0 : E) 1] using hz))
  have hvdet : ∀ z ∈ interior (closedBall (0 : E) 1),
      (1+complexHessian realDirections imagDirections v z).det = 1 := by
    intro z hz
    rw [hH z hz]
    exact hdet (T z) (hmap (by simpa only [interior_closedBall' (0 : E) 1] using hz))
  have hvbound : ∀ z ∈ closedBall (0 : E) 1,
      0 ≤ v z ∧ v z ≤ (r^2)⁻¹*ε := by
    intro z hz
    obtain ⟨hl,hu⟩ := hbound (T z) (hmapcl hz)
    change 0 ≤ (r^2)⁻¹*(w (T z)-m) ∧ (r^2)⁻¹*(w (T z)-m) ≤ (r^2)⁻¹*ε
    exact ⟨mul_nonneg hi.le (sub_nonneg.mpr hl),
      mul_le_mul_of_nonneg_left (by linarith only [hu]) hi.le⟩
  have hsmall' : (r^2)⁻¹*ε ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hsmall hi.le
    simpa only [inv_mul_cancel₀ hr2.ne'] using hh
  have himprove := hstep v hvc hv hvpsh hvdet ((r^2)⁻¹*ε) (mul_pos hi hε) hsmall' hvbound
  have hinverse (x : E) : T (r⁻¹ • (x-c)) = x := by
    dsimp only [T]
    rw [smul_smul,mul_inv_cancel₀ hr.ne',one_smul,add_sub_cancel]
  have hnorm (x : E) (hx : x ∈ closedBall c (r/32)) :
      r⁻¹ • (x-c) ∈ closedBall (0 : E) (1/32 : ℝ) := by
    rw [mem_closedBall,dist_zero_right,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
    apply (inv_mul_le_iff₀ hr).mpr
    simpa only [mem_closedBall,dist_eq_norm,div_eq_mul_inv,one_mul] using hx
  intro x hx y hy
  let X := r⁻¹ • (x-c)
  let Y := r⁻¹ • (y-c)
  have hX : X ∈ closedBall (0 : E) (1/32 : ℝ) := hnorm x hx
  have hY : Y ∈ closedBall (0 : E) (1/32 : ℝ) := hnorm y hy
  have hX1 := (closedBall_subset_closedBall (by norm_num : (1/32 : ℝ) ≤ 1)) hX
  have hY1 := (closedBall_subset_closedBall (by norm_num : (1/32 : ℝ) ≤ 1)) hY
  have hvdiff : v X-v Y ≤ (1-κ)*((r^2)⁻¹*ε) := by
    rcases himprove with hl | hu
    · have hlow := hl Y hY
      have hupp := (hvbound X hX1).2
      linarith only [hlow,hupp]
    · have hupp := hu X hX
      have hlow := (hvbound Y hY1).1
      linarith only [hlow,hupp]
  have hvX : v X = (r^2)⁻¹*(w x-m) := by change (r^2)⁻¹*(w (T X)-m) = _; rw [hinverse]
  have hvY : v Y = (r^2)⁻¹*(w y-m) := by change (r^2)⁻¹*(w (T Y)-m) = _; rw [hinverse]
  rw [hvX,hvY] at hvdiff
  have hh : (r^2)⁻¹*(w x-w y) ≤ (r^2)⁻¹*((1-κ)*ε) := by nlinarith only [hvdiff]
  exact le_of_mul_le_mul_left hh hi

end PowerConvexity
