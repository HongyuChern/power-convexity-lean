import PowerConvexity.Analysis.ActualContinuousWeakQuadraticClassicalTwo
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-! # Actual directional derivatives recover higher regularity

The derivative in these statements is the genuine Frechet derivative on
the same open set.  No extension or unidentified derivative field is used.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_contDiffOn_succ_of_actual_directionals_two
    {U : Set E} (hU : IsOpen U) {u : E → ℝ} {n : ℕ}
    (hu : DifferentiableOn ℝ u U)
    (hd : ∀ v : E, ContDiffOn ℝ n (fun x => fderiv ℝ u x v) U) :
    ContDiffOn ℝ (n+1) u U := by
  apply contDiffOn_succ_of_fderiv_apply hu
  · simp
  · intro v
    apply (hd v).congr
    intro x hx
    rw [fderivWithin_of_mem_nhds (hU.mem_nhds hx)]

theorem actual_C3_of_C1_directional_C2_two
    {U : Set E} (hU : IsOpen U) {u : E → ℝ}
    (hu : ContDiffOn ℝ 1 u U)
    (hd : ∀ v : E, ContDiffOn ℝ 2 (fun x => fderiv ℝ u x v) U) :
    ContDiffOn ℝ 3 u U := by
  exact actual_contDiffOn_succ_of_actual_directionals_two hU
    (hu.differentiableOn (by norm_num)) hd

theorem actual_directional_regular_of_unit_directions_two
    {U : Set E} {u : E → ℝ} {n : ℕ}
    (hd : ∀ v : E, ‖v‖ ≤ 1 → ContDiffOn ℝ n (fun x => fderiv ℝ u x v) U) :
    ∀ v : E, ContDiffOn ℝ n (fun x => fderiv ℝ u x v) U := by
  intro v
  by_cases hv : v=0
  · simpa only [hv,map_zero] using (contDiffOn_const : ContDiffOn ℝ n (fun _ : E => (0 : ℝ)) U)
  · have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    have hunit : ‖‖v‖⁻¹ • v‖ ≤ 1 := by
      rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_norm,inv_mul_cancel₀ hn]
    have he : (fun x => fderiv ℝ u x v)=
        (fun x => ‖v‖*fderiv ℝ u x (‖v‖⁻¹ • v)) := by
      funext x
      rw [map_smul,smul_eq_mul,← mul_assoc,mul_inv_cancel₀ hn,one_mul]
    rw [he]
    exact contDiffOn_const.mul (hd (‖v‖⁻¹ • v) hunit)

theorem actual_C3_of_C1_unit_directional_C2_two
    {U : Set E} (hU : IsOpen U) {u : E → ℝ}
    (hu : ContDiffOn ℝ 1 u U)
    (hd : ∀ v : E, ‖v‖ ≤ 1 → ContDiffOn ℝ 2 (fun x => fderiv ℝ u x v) U) :
    ContDiffOn ℝ 3 u U :=
  actual_C3_of_C1_directional_C2_two hU hu (actual_directional_regular_of_unit_directions_two hd)

theorem actual_C4_of_C2_second_directional_C2_two
    {U : Set E} (hU : IsOpen U) {u : E → ℝ}
    (hu : ContDiffOn ℝ 2 u U)
    (hdd : ∀ v w : E, ContDiffOn ℝ 2
      (fun x => fderiv ℝ (fun y => fderiv ℝ u y v) x w) U) :
    ContDiffOn ℝ 4 u U := by
  apply actual_contDiffOn_succ_of_actual_directionals_two hU
    (hu.differentiableOn (by norm_num))
  intro v
  exact actual_C3_of_C1_directional_C2_two hU
    ((hu.fderiv_of_isOpen hU (m := 1) (by norm_num)).clm_apply contDiffOn_const)
    (hdd v)

end PowerConvexity
