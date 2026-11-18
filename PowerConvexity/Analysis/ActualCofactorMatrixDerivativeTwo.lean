import PowerConvexity.Analysis.ActualCofactorHolderMapTwo
import PowerConvexity.Calculus.ActualHigherDerivativeIdentitiesTwo

/-! # Exact derivatives of the same actual cofactor matrix -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
open Set Filter Metric Matrix
open scoped ContDiff Topology BigOperators Matrix.Norms.Elementwise
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ
local notation "Mat" => Matrix (Fin (2+2)) (Fin (2+2)) ℝ
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

def actualCofactorMatrixFormTwo : Bilin →L[ℝ] Mat :=
  actualRealWeightLinearTwo.comp (actualAdjugateLinearTwo.comp actualComplexHessianFormTwo)

theorem actual_cofactor_matrix_form_eq_two {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) :
    actualCofactorMatrixFormTwo (realHessian u x) = complexCofactorCoeff u x := by
  change realLinearizedWeight (actualComplexHessianFormTwo (realHessian u x)).adjugate = _
  rw [actual_complex_Hessian_form_eq_two hu]
  rfl

theorem actual_scaled_cofactor_entry_derivative_two
    {U : Set E} (hU : IsOpen U) {u : E → ℝ} (hu : ContDiffOn ℝ 4 u U)
    {a : E → Mat} {c : ℝ} (ha : ∀ y ∈ U, a y = c⁻¹ • complexCofactorCoeff u y)
    {x : E} (hx : x ∈ U) (v : E) (i j : Fin (2+2)) :
    fderiv ℝ (fun y => a y i j) x v =
      c⁻¹*actualCofactorMatrixFormTwo (fderiv ℝ (realHessian u) x v) i j := by
  have hu4 := hu.contDiffAt (hU.mem_nhds hx)
  have hH : DifferentiableAt ℝ (realHessian u) x :=
    ((hu4.fderiv_right (m := 3) (by norm_num)).fderiv_right
      (m := 2) (by norm_num)).differentiableAt (by norm_num)
  have he : (fun y => a y i j) =ᶠ[𝓝 x]
      (fun y => c⁻¹*actualCofactorMatrixFormTwo (realHessian u y) i j) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    rw [ha y hy,actual_cofactor_matrix_form_eq_two
      ((hu.contDiffAt (hU.mem_nhds hy)).of_le (by norm_num))]
    rfl
  let ev : Mat →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj j : (Fin (2+2) → ℝ) →L[ℝ] ℝ).comp
      (ContinuousLinearMap.proj i : Mat →L[ℝ] (Fin (2+2) → ℝ))
  have hd := ((ev.comp actualCofactorMatrixFormTwo).hasFDerivAt.comp x hH.hasFDerivAt).const_mul c⁻¹
  have hev (M : Mat) : ev M = M i j := rfl
  rw [he.fderiv_eq]
  have hh := congrArg (fun L : E →L[ℝ] ℝ => L v) hd.fderiv
  simpa only [Function.comp_apply,ContinuousLinearMap.comp_apply,
    hev,_root_.smul_apply,smul_eq_mul] using hh

theorem actual_cofactor_matrix_entry_norm_bound_two (H : Bilin) (i j : Fin (2+2)) :
    |actualCofactorMatrixFormTwo H i j| ≤ ‖actualCofactorMatrixFormTwo‖*‖H‖ := by
  have hh : ‖actualCofactorMatrixFormTwo H i j‖ ≤ ‖actualCofactorMatrixFormTwo H‖ :=
    (norm_le_pi_norm _ j).trans (norm_le_pi_norm _ i)
  rw [Real.norm_eq_abs] at hh
  exact hh.trans (actualCofactorMatrixFormTwo.le_opNorm H)

end PowerConvexity
