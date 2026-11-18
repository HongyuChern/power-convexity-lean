import PowerConvexity.Calculus.SmallValueContactMeasureTwo
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! # Quantitative geometry of the actual contact-growth vertices.
These lemmas concern the weighted vertices used in the sliding argument.
The volume comparison is for the actual four-dimensional Lebesgue measure.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal Topology
namespace PowerConvexity
local notation "E" => DeGiorgi.AmbientSpace (2+2)

theorem weighted_contact_vertices_contain_small_ball_two
    {M r : ℝ} (hM : 2 ≤ M) (hr : 0 < r) (y1 z : E) :
    closedBall (M⁻¹ • (y1+(M-1) • z)) (r/128) ⊆
      (fun y : E => M⁻¹ • (y1+(M-1) • y)) '' closedBall z (r/64) := by
  have hMp : 0 < M := by linarith only [hM]
  have hMm : 0 < M-1 := by linarith only [hM]
  have hc : 0 < M/(M-1) := div_pos hMp hMm
  have hc2 : M/(M-1) ≤ 2 := (div_le_iff₀ hMm).mpr (by linarith only [hM])
  let Y : E → E := fun y => M⁻¹ • (y1+(M-1) • y)
  intro p hp
  have hpn : ‖p-Y z‖ ≤ r/128 := by simpa only [Y,mem_closedBall,dist_eq_norm] using hp
  let y : E := z+(M/(M-1)) • (p-Y z)
  have hyz : y-z = (M/(M-1)) • (p-Y z) := by dsimp only [y]; module
  have hyn : ‖y-z‖ ≤ r/64 := by
    rw [hyz,norm_smul,Real.norm_eq_abs,abs_of_pos hc]
    calc
      M/(M-1)*‖p-Y z‖ ≤ 2*‖p-Y z‖ := mul_le_mul_of_nonneg_right hc2 (norm_nonneg _)
      _ ≤ 2*(r/128) := mul_le_mul_of_nonneg_left hpn (by norm_num)
      _ = r/64 := by ring
  refine ⟨y,by simpa only [mem_closedBall,dist_eq_norm] using hyn,?_⟩
  have hd : Y y-Y z = (M⁻¹*(M-1)) • (y-z) := by dsimp only [Y]; module
  rw [hyz,smul_smul] at hd
  have hs : (M⁻¹*(M-1))*(M/(M-1)) = 1 := by field_simp
  rw [hs,one_smul] at hd
  exact sub_left_inj.mp hd

theorem closedBall_radius_div_128_volume_two (c d : E) (r : ℝ) :
    volume (closedBall d r) = ENNReal.ofReal ((128 : ℝ)^4)*volume (closedBall c (r/128)) := by
  have hdim : Module.finrank ℝ E = 4 := by simp [DeGiorgi.AmbientSpace]
  have h := Measure.addHaar_closedBall_mul_of_pos volume d (by norm_num : (0 : ℝ) < 128) (r/128)
  rw [hdim] at h
  rw [Measure.addHaar_closedBall_center volume c]
  have hradius : (128 : ℝ)*(r/128) = r := by ring
  rw [hradius] at h
  exact h

end PowerConvexity
