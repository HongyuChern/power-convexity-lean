import PowerConvexity.Calculus.SmallValueContactMeasureTwo
import Mathlib.MeasureTheory.Measure.Real

/-! # Finite-measure contraction from actual growth of nested sets.
Finiteness is checked before passing from extended to real-valued measure.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace PowerConvexity
local notation "E" => DeGiorgi.AmbientSpace (2+2)

theorem contact_complement_real_measure_contraction_two
    {U F G : Set E} (hU : volume U ≠ ∞)
    (hF : MeasurableSet F) (hG : MeasurableSet G)
    (hFG : F ⊆ G) (hGU : G ⊆ U) {C : ℝ} (hC : 0 < C)
    (hgrowth : volume (U \ F) ≤ ENNReal.ofReal C*volume (G \ F)) :
    volume.real (U \ G) ≤ (1-(C+1)⁻¹)*volume.real (U \ F) := by
  have hFU : F ⊆ U := hFG.trans hGU
  have hGn : volume G ≠ ∞ := measure_ne_top_of_subset hGU hU
  have hGF : volume (G \ F) ≠ ∞ := measure_ne_top_of_subset sdiff_subset hGn
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hGF) hgrowth
  simp only [ENNReal.toReal_mul,ENNReal.toReal_ofReal hC.le,← measureReal_def] at hreal
  have hnon : 0 ≤ volume.real (G \ F) := measureReal_nonneg
  have hinc : volume.real (U \ F) ≤ (C+1)*volume.real (G \ F) := by
    nlinarith only [hreal,hnon]
  have hCp : 0 < C+1 := by positivity
  have hfrac : (C+1)⁻¹*volume.real (U \ F) ≤ volume.real (G \ F) := by
    calc
      _ ≤ (C+1)⁻¹*((C+1)*volume.real (G \ F)) :=
        mul_le_mul_of_nonneg_left hinc (inv_pos.mpr hCp).le
      _ = volume.real (G \ F) := by field_simp
  have hidentity : volume.real (U \ G) = volume.real (U \ F)-volume.real (G \ F) := by
    rw [measureReal_sdiff hGU hG hU,measureReal_sdiff hFU hF hU,
      measureReal_sdiff hFG hF hGn]
    ring
  rw [hidentity]
  nlinarith only [hfrac]

end PowerConvexity
