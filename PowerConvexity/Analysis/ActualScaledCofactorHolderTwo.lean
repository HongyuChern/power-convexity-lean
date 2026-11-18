import PowerConvexity.Analysis.ActualCofactorHolderMapTwo
import PowerConvexity.Calculus.RealHessianBlockNormTwo

/-! # The same normalized cofactor inherits the actual Hessian Holder modulus -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
local notation "Mat" => Matrix (Fin (2+2)) (Fin (2+2)) ℝ
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_scaled_cofactor_operator_Holder_bound_two
    {u : E → ℝ} {x y : E} (hux : ContDiffAt ℝ 2 u x) (huy : ContDiffAt ℝ 2 u y)
    {a : E → Mat} {c K alpha : ℝ} (hc : 0 < c)
    (hax : a x = c⁻¹ • complexCofactorCoeff u x)
    (hay : a y = c⁻¹ • complexCofactorCoeff u y)
    (hhold : ‖realHessian u x-realHessian u y‖ ≤ K*‖x-y‖^alpha) :
    ‖actualMatrixOperatorTwo (a x)-actualMatrixOperatorTwo (a y)‖ ≤
      (c⁻¹*‖actualCofactorOperatorFormTwo‖*K)*‖x-y‖^alpha := by
  have hh := actual_cofactor_operator_Holder_bound_two hux huy hhold
  have he : c⁻¹ • actualMatrixOperatorTwo (complexCofactorCoeff u x)-
      c⁻¹ • actualMatrixOperatorTwo (complexCofactorCoeff u y) =
      c⁻¹ • (actualMatrixOperatorTwo (complexCofactorCoeff u x)-
        actualMatrixOperatorTwo (complexCofactorCoeff u y)) := by
    ext v i
    change c⁻¹*(actualMatrixOperatorTwo (complexCofactorCoeff u x) v i)-
      c⁻¹*(actualMatrixOperatorTwo (complexCofactorCoeff u y) v i) =
      c⁻¹*(actualMatrixOperatorTwo (complexCofactorCoeff u x) v i-
        actualMatrixOperatorTwo (complexCofactorCoeff u y) v i)
    ring
  rw [hax,hay,map_smul,map_smul,he,norm_smul,Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hc)]
  exact (mul_le_mul_of_nonneg_left hh (inv_pos.mpr hc).le).trans_eq (by ring)

theorem actual_scaled_cofactor_operator_Holder_of_block_two
    {u : E → ℝ} {x y : E} (hux : ContDiffAt ℝ 2 u x) (huy : ContDiffAt ℝ 2 u y)
    {a : E → Mat} {c K alpha : ℝ} (hc : 0 < c)
    (hax : a x = c⁻¹ • complexCofactorCoeff u x)
    (hay : a y = c⁻¹ • complexCofactorCoeff u y)
    (hhold : ‖realBlockHessian realDirections imagDirections u x-
      realBlockHessian realDirections imagDirections u y‖ ≤ K*‖x-y‖^alpha) :
    ‖actualMatrixOperatorTwo (a x)-actualMatrixOperatorTwo (a y)‖ ≤
      (c⁻¹*‖actualCofactorOperatorFormTwo‖*(16*K))*‖x-y‖^alpha := by
  apply actual_scaled_cofactor_operator_Holder_bound_two hux huy hc hax hay
  exact (realHessian_norm_sub_le_sixteen_block_norm_two u x y).trans
    ((mul_le_mul_of_nonneg_left hhold (by norm_num : (0 : ℝ) ≤ 16)).trans_eq (by ring))

end PowerConvexity
