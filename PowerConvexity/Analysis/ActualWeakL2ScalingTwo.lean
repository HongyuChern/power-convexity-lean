import PowerConvexity.Analysis.ActualScalarInteriorEnergyTwo
import DifferentialGeometry.External.DeGiorgi.Crossover.LocalIntegrability

/-! # Exact value and gradient L2 scaling in real dimension four.
These identities use the actual affine pullback and actual weak-gradient
witness. The two scaling exponents differ by two, as required in the
local scalar equation iteration.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "F" => AmbientSpace (2+2)

theorem actual_scalar_L2_rescale_squared_two {c : F} {R : ℝ} (hR : 0 < R)
    {u : F → ℝ} (hu : MemLp u 2 (volume.restrict (ball c R)))
    (hr : MemLp (rescaleToUnitBall (x₀ := c) (R := R) u) 2 (volume.restrict (ball (0 : F) 1))) :
    ‖hr.toLp (rescaleToUnitBall (x₀ := c) (R := R) u)‖^2 =
      (R^4)⁻¹*‖hu.toLp u‖^2 := by
  rw [actual_scalar_L2_norm_squared_two,actual_scalar_L2_norm_squared_two]
  have hh := crossover_integral_comp_affine_ball (x₀ := c) (ρ := (1 : ℝ)) hR
    (fun x => (u x)^2)
  simpa [rescaleToUnitBall,AmbientSpace] using hh

theorem actual_gradient_L2_rescale_squared_two {c : F} {R : ℝ} (hR : 0 < R)
    {u : F → ℝ} (uw : MemW1pWitness 2 u (ball c R)) :
    ‖gradLpOfWitness (uw.rescaleToUnitBall hR)‖^2 =
      (R^2)⁻¹*‖gradLpOfWitness uw‖^2 := by
  rw [actual_gradLp_norm_squared_two,actual_gradLp_norm_squared_two]
  have hh := crossover_integral_comp_affine_ball (x₀ := c) (ρ := (1 : ℝ)) hR
    (fun x => ‖uw.weakGrad x‖^2)
  have hh' : (∫ x in ball (0 : F) 1, ‖uw.weakGrad (c+R • x)‖^2) =
      (R^4)⁻¹*(∫ x in ball c R, ‖uw.weakGrad x‖^2) := by
    simpa [AmbientSpace] using hh
  calc
    (∫ x in ball (0 : F) 1, ‖(uw.rescaleToUnitBall hR).weakGrad x‖^2)
        = ∫ x in ball (0 : F) 1, R^2*‖uw.weakGrad (c+R • x)‖^2 := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by
        simp only [MemW1pWitness.rescaleToUnitBall,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs])
    _ = R^2*(∫ x in ball (0 : F) 1, ‖uw.weakGrad (c+R • x)‖^2) := integral_const_mul _ _
    _ = R^2*((R^4)⁻¹*(∫ x in ball c R, ‖uw.weakGrad x‖^2)) := by rw [hh']
    _ = (R^2)⁻¹*(∫ x in ball c R, ‖uw.weakGrad x‖^2) := by field_simp

end PowerConvexity
