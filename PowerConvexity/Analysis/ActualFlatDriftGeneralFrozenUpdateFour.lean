import PowerConvexity.Analysis.ActualFlatDriftFrozenUpdateFour

/-! # The full frozen equation survives lifting an arbitrary residual -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_flat_drift_quadratic_update_general_frozen_four {q p : E → ℝ}
    (hq : IsQuadraticPolynomial q) (hp : IsQuadraticPolynomial p)
    {R a : ℝ} (hR : 0 < R) (ha : 0 < a) (b0 : E) (f0 : ℝ)
    (hpt : (realBlockHessian realDirections imagDirections p 0).trace+fderiv ℝ p 0 (R • b0) =
      -a⁻¹*(f0+(realBlockHessian realDirections imagDirections q 0).trace+fderiv ℝ q 0 b0)) :
    (realBlockHessian realDirections imagDirections (scalarQuadraticUpdateTwo q p R a) 0).trace+
      fderiv ℝ (scalarQuadraticUpdateTwo q p R a) 0 b0 = -f0 := by
  have hd := congrArg (fun L : E →L[ℝ] ℝ => L b0)
    (scalarQuadraticUpdateTwo_jet_increments (a := a) hq hp hR).2.1
  simp only [_root_.sub_apply,_root_.smul_apply,smul_eq_mul] at hd
  have ht := actual_quadratic_update_trace_four (a := a) hq hp hR (0 : E)
  rw [smul_zero] at ht
  rw [map_smul,smul_eq_mul] at hpt
  have hm := congrArg (fun t : ℝ => a*t) hpt
  have he : a*(-a⁻¹*(f0+(realBlockHessian realDirections imagDirections q 0).trace+fderiv ℝ q 0 b0)) =
      -(f0+(realBlockHessian realDirections imagDirections q 0).trace+fderiv ℝ q 0 b0) := by field_simp
  rw [he] at hm
  rw [ht]
  linear_combination hd + hm

end PowerConvexity
