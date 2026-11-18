import PowerConvexity.Analysis.ActualScalarGeneralSourceExpansionTwo
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! # Actual change of variables under an invertible linear map.
The domain is the actual preimage and the Jacobian is the determinant
of the given map. These identities will be used for weak derivatives.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_linear_map_volume_two (G : E ≃L[ℝ] E) :
    Measure.map G (volume : Measure E) =
      ENNReal.ofReal |(LinearMap.det G.toLinearMap)⁻¹| • volume := by
  exact Measure.map_linearMap_addHaar_eq_smul_addHaar volume
    (LinearEquiv.isUnit_det' G.toLinearEquiv).ne_zero

theorem actual_linear_jacobian_pos_two (G : E ≃L[ℝ] E) :
    0 < |(LinearMap.det G.toLinearMap)⁻¹| := by
  exact abs_pos.mpr (inv_ne_zero (LinearEquiv.isUnit_det' G.toLinearEquiv).ne_zero)

theorem actual_memLp_linear_pullback_two {p : ENNReal} {U : Set E} {f : E → ℝ}
    (G : E ≃L[ℝ] E) (hf : MemLp f p (volume.restrict U)) :
    MemLp (fun z => f (G z)) p (volume.restrict (G ⁻¹' U)) := by
  have hG : MeasurableEmbedding G := G.toHomeomorph.toMeasurableEquiv.measurableEmbedding
  rw [show (fun z => f (G z)) = f ∘ G from rfl,
    ← hG.memLp_map_measure_iff,← hG.restrict_map,
    actual_linear_map_volume_two,Measure.restrict_smul]
  exact hf.smul_measure ENNReal.ofReal_ne_top

theorem actual_setIntegral_linear_pullback_two {U : Set E} (G : E ≃L[ℝ] E)
    (f : E → ℝ) :
    (∫ z in G ⁻¹' U, f (G z)) =
      |(LinearMap.det G.toLinearMap)⁻¹| * ∫ x in U, f x := by
  have hG : MeasurableEmbedding G := G.toHomeomorph.toMeasurableEquiv.measurableEmbedding
  rw [← hG.integral_map,← hG.restrict_map,actual_linear_map_volume_two,
    Measure.restrict_smul,integral_smul_measure,ENNReal.toReal_ofReal (abs_nonneg _)]
  rfl

end PowerConvexity
