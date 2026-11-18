import PowerConvexity.Calculus.ChordDefectCalculus
import Mathlib.Analysis.Convex.Topology

/-! # Excluding a boundary maximum of the chord defect

The boundary input is stated in the square-root scale s. It is later obtained
from a linear upper barrier for u along the segment into the domain.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open Set Filter
open scoped Topology
namespace PowerConvexity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def HasQuadraticBoundaryDecay (f : E → ℝ) (U : Set E) : Prop :=
  ∀ x ∈ frontier U, ∀ y ∈ U, ∃ c > 0, ∃ δ > 0,
    ∀ s : ℝ, 0 < s → s < δ →
      x+s^2 • (y-x) ∈ U ∧ f (x+s^2 • (y-x)) ≤ -c*s

theorem chordDefect_swap (a b : ℝ) (f : E → ℝ) (x y : E) :
    chordDefect a b f (x,y) = chordDefect b a f (y,x) := by
  simp only [chordDefect,add_comm (b • y) (a • x)]
  ring

theorem chordDefect_boundary_left_improves
    {f : E → ℝ} {U : Set E} {x y : E} {a b : ℝ}
    (ha : 0 < a) (hfx : f x = 0)
    (hfz : DifferentiableAt ℝ f (a • x+b • y))
    (hdecay : ∃ c > 0, ∃ δ > 0, ∀ s : ℝ, 0 < s → s < δ →
      x+s^2 • (y-x) ∈ U ∧ f (x+s^2 • (y-x)) ≤ -c*s) :
    ∃ w ∈ U, chordDefect a b f (x,y) < chordDefect a b f (w,y) := by
  let z := a • x+b • y
  let d := y-x
  let q : ℝ → E := fun s => a • (x+s^2 • d)+b • y
  obtain ⟨c,hc,δ,hδ,hdec⟩ := hdecay
  obtain ⟨C,hC,hbound⟩ := hfz.isBigO_sub.exists_pos
  have hq : Tendsto q (𝓝 (0:ℝ)) (𝓝 z) := by
    have hh : ContinuousAt q 0 := by dsimp [q]; fun_prop
    simpa only [q,z,zero_pow (by decide : 2 ≠ 0),zero_smul,add_zero] using hh.tendsto
  have hev : ∀ᶠ s in 𝓝 (0:ℝ), ‖f (q s)-f z‖ ≤ C*‖q s-z‖ := hq.eventually hbound.bound
  obtain ⟨η,hη,hηball⟩ := Metric.mem_nhds_iff.mp hev
  let D := C*a*‖d‖
  have hD : 0 ≤ D := mul_nonneg (mul_nonneg hC.le ha.le) (norm_nonneg _)
  have heps : 0 < min δ (min η (min 1 (a*c/(D+1)))) :=
    lt_min hδ (lt_min hη (lt_min (by norm_num) (div_pos (mul_pos ha hc) (by linarith))))
  obtain ⟨s,hs,hsall⟩ := exists_between heps
  have hsδ : s < δ := hsall.trans_le (min_le_left _ _)
  have hsη : s < η := hsall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hsbound : s < a*c/(D+1) := hsall.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hsmall : D*s < a*c := by
    have hh := (lt_div_iff₀ (by linarith : 0 < D+1)).mp hsbound
    nlinarith
  have hsball : s ∈ Metric.ball (0:ℝ) η := by
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos hs] using hsη
  have hh := hηball hsball
  change ‖f (q s)-f z‖ ≤ C*‖q s-z‖ at hh
  have hqdiff : q s-z = (a*s^2) • d := by dsimp [q,z]; module
  simp only [hqdiff,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg ha.le (sq_nonneg s))] at hh
  have hlower : -D*s^2 ≤ f (q s)-f z := by
    have hh' := (abs_le.mp hh).1
    dsimp [D]
    nlinarith
  obtain ⟨hw,hfw⟩ := hdec s hs hsδ
  refine ⟨x+s^2 • (y-x),hw,?_⟩
  have hmul := mul_le_mul_of_nonneg_left hfw ha.le
  have hgain : 0 < s*(a*c-D*s) := mul_pos hs (sub_pos.mpr hsmall)
  change f z-a*f x-b*f y < f (q s)-a*f (x+s^2 • (y-x))-b*f y
  rw [hfx,mul_zero]
  nlinarith

end PowerConvexity
