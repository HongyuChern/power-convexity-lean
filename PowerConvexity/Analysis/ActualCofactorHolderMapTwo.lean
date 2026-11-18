import PowerConvexity.Analysis.ActualNormalizedCoefficientScaleTwo
import PowerConvexity.Calculus.VariableDensityCofactor

/-! # The actual two-dimensional cofactor is a fixed linear map of real Hessians

This uses linearity of the 2 by 2 adjugate. It gives coefficient Holder bounds
without differentiating the unknown solution a third time.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators Matrix.Norms.Elementwise
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ
local notation "Mat" => Matrix (Fin (2+2)) (Fin (2+2)) ℝ
local notation "CMat" => Matrix (Fin 2) (Fin 2) ℂ
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

def actualComplexHessianFormTwo : Bilin →L[ℝ] CMat :=
  ({ toFun := fun H i j => (4 : ℂ)⁻¹ *
      ((H (realDirections i) (realDirections j) : ℂ) +
        (H (imagDirections i) (imagDirections j) : ℂ) + Complex.I *
        ((H (realDirections i) (imagDirections j) : ℂ) -
          (H (imagDirections i) (realDirections j) : ℂ)))
     map_add' := by
       intro H K
       ext i j
       simp only [_root_.add_apply,Matrix.add_apply,Complex.ofReal_add]
       ring
     map_smul' := by
       intro r H
       ext i j
       simp only [_root_.smul_apply,Matrix.smul_apply,smul_eq_mul,Complex.ofReal_mul,
         Complex.real_smul,RingHom.id_apply]
       ring } : Bilin →ₗ[ℝ] CMat).toContinuousLinearMap

theorem actual_complex_Hessian_form_eq_two {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) :
    actualComplexHessianFormTwo (realHessian u x) =
      complexHessian realDirections imagDirections u x := by
  ext i j
  exact (complexHessian_real_entry hu realDirections imagDirections i j).symm

def actualAdjugateLinearTwo : CMat →L[ℝ] CMat :=
  ({ toFun := Matrix.adjugate
     map_add' := by
       intro A B
       ext i j
       fin_cases i <;> fin_cases j <;> simp [Matrix.adjugate_fin_two,add_comm]
     map_smul' := by
       intro r A
       ext i j
       fin_cases i <;> fin_cases j <;> simp [Matrix.adjugate_fin_two,smul_neg] } :
    CMat →ₗ[ℝ] CMat).toContinuousLinearMap

def actualRealWeightLinearTwo : CMat →L[ℝ] Mat :=
  { toLinearMap :=
      { toFun := realLinearizedWeight
        map_add' := by
          intro A B
          have he : realLinearizationMatrix (A+B) = realLinearizationMatrix A+realLinearizationMatrix B := by
            ext i j
            rcases i with i | i <;> rcases j with j | j <;>
              simp [realLinearizationMatrix] <;> ring
          ext i j
          simpa only [realLinearizedWeight,Matrix.reindex_apply,Matrix.submatrix_apply,
            Matrix.add_apply] using congrArg
              (fun M => M (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)) he
        map_smul' := realLinearizedWeight_real_smul }
    cont := continuous_realLinearizedWeight }

def actualCofactorOperatorFormTwo : Bilin →L[ℝ] (E →L[ℝ] E) :=
  actualMatrixOperatorTwo.comp (actualRealWeightLinearTwo.comp
    (actualAdjugateLinearTwo.comp actualComplexHessianFormTwo))

theorem actual_cofactor_operator_form_eq_two {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) :
    actualCofactorOperatorFormTwo (realHessian u x) =
      actualMatrixOperatorTwo (complexCofactorCoeff u x) := by
  change actualMatrixOperatorTwo
    (realLinearizedWeight (actualComplexHessianFormTwo (realHessian u x)).adjugate) = _
  rw [actual_complex_Hessian_form_eq_two hu]
  rfl

theorem actual_cofactor_operator_Holder_bound_two
    {u : E → ℝ} {x y : E} (hux : ContDiffAt ℝ 2 u x) (huy : ContDiffAt ℝ 2 u y)
    {K alpha : ℝ}
    (hhold : ‖realHessian u x-realHessian u y‖ ≤ K*‖x-y‖^alpha) :
    ‖actualMatrixOperatorTwo (complexCofactorCoeff u x)-
      actualMatrixOperatorTwo (complexCofactorCoeff u y)‖ ≤
        (‖actualCofactorOperatorFormTwo‖*K)*‖x-y‖^alpha := by
  rw [← actual_cofactor_operator_form_eq_two hux,← actual_cofactor_operator_form_eq_two huy,
    ← map_sub]
  exact (actualCofactorOperatorFormTwo.le_opNorm _).trans
    ((mul_le_mul_of_nonneg_left hhold (norm_nonneg _)).trans_eq (by ring))

end PowerConvexity
