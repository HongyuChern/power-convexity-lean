import PowerConvexity.Analysis.ActualScalarQuadraticLimitErrorTwo

/-! # Removing the constant scalar source by an actual particular quadratic.
The sign is that of the full weak equation: -div(A grad u)=f.
For A(0)=I in real dimension four, q=-b*|x|^2/8 has source b at zero.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

def scalarConstantSourceQuadraticTwo (b : ℝ) (x : E) : ℝ := (-b/8)*‖x‖^2

theorem scalarConstantSourceQuadraticTwo_isQuadratic (b : ℝ) :
    IsQuadraticPolynomial (scalarConstantSourceQuadraticTwo b) :=
  IsQuadraticPolynomial_const_mul norm_sq_isQuadraticPolynomial_four _

theorem scalarConstantSourceQuadraticTwo_Hessian_bound (b : ℝ) (x : E) :
    ‖realHessian (scalarConstantSourceQuadraticTwo b) x‖ ≤ |b|/4 := by
  change ‖realHessian (fun y : E => (-b/8)*‖y‖^2) x‖ ≤ _
  rw [realHessian_const_mul,norm_smul,Real.norm_eq_abs,abs_div,abs_neg]
  rw [show |(8 : ℝ)| = 8 by norm_num]
  exact (mul_le_mul_of_nonneg_left (actual_norm_square_Hessian_norm_le_two_four x)
    (by positivity : 0 ≤ |b|/8)).trans_eq (by ring)

theorem scalarConstantSourceQuadraticTwo_source
    (a : E → Matrix (Fin (2+2)) (Fin (2+2)) ℝ) (b : ℝ) (x : E) :
    quadraticScalarSourceTwo a (scalarConstantSourceQuadraticTwo b) x = (b/4)*(a x).trace := by
  have hentry (i j : Fin (2+2)) :
      euclideanHessian (scalarConstantSourceQuadraticTwo b) x i j =
        (-b/4)*(if i = j then 1 else 0) := by
    change realHessian (fun y : E => (-b/8)*‖y‖^2) x
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) = _
    rw [realHessian_const_mul]
    simp only [_root_.smul_apply,smul_eq_mul,realHessian_norm_square,
      orthonormal_iff_ite.mp (EuclideanSpace.orthonormal_single (𝕜 := ℝ))]
    ring
  simp only [quadraticScalarSourceTwo,hentry,mul_ite,mul_zero,mul_one,
    Finset.sum_ite_eq,Finset.mem_univ,if_true]
  rw [← Finset.sum_mul]
  simp only [Matrix.trace,Matrix.diag_apply]
  ring

theorem actual_identity_coefficient_trace_error_two
    {a : Matrix (Fin (2+2)) (Fin (2+2)) ℝ} {delta : ℝ}
    (ha : ∀ z : E, ‖z-matMulE a z‖ ≤ delta*‖z‖) :
    |a.trace-4| ≤ 4*delta := by
  have he : a.trace-4 = ∑ i : Fin (2+2), (a i i-1) := by
    simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
      Nat.reduceAdd,nsmul_eq_mul,Matrix.trace,Matrix.diag_apply]
    norm_num
  rw [he]
  calc
    _ ≤ ∑ i : Fin (2+2), |a i i-1| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (2+2), delta := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [Matrix.one_apply,ite_true] using actual_identity_coefficient_entry_bound_two ha i i
    _ = _ := by simp

theorem actual_constant_source_correction_error_two
    {a : E → Matrix (Fin (2+2)) (Fin (2+2)) ℝ} {b delta : ℝ} {x : E}
    (ha : ∀ z : E, ‖z-matMulE (a x) z‖ ≤ delta*‖z‖) :
    |quadraticScalarSourceTwo a (scalarConstantSourceQuadraticTwo b) x-b| ≤ |b| *delta := by
  rw [scalarConstantSourceQuadraticTwo_source]
  have he : (b/4)*(a x).trace-b = (b/4)*((a x).trace-4) := by ring
  rw [he,abs_mul,abs_div]
  rw [show |(4 : ℝ)| = 4 by norm_num]
  exact (mul_le_mul_of_nonneg_left (actual_identity_coefficient_trace_error_two ha)
    (by positivity : 0 ≤ |b|/4)).trans_eq (by ring)

theorem actual_constant_corrected_source_growth_two
    {a : E → Matrix (Fin (2+2)) (Fin (2+2)) ℝ} {f : E → ℝ}
    {b epsilon K : ℝ} {U : Set E}
    (ha : ∀ x ∈ U, ∀ z : E, ‖z-matMulE (a x) z‖ ≤ (epsilon*‖x‖)*‖z‖)
    (hf : ∀ x ∈ U, |f x-b| ≤ K*‖x‖) :
    ∀ x ∈ U, |f x-quadraticScalarSourceTwo a (scalarConstantSourceQuadraticTwo b) x| ≤
      (K+|b| *epsilon)*‖x‖ := by
  intro x hx
  have hq := actual_constant_source_correction_error_two (b := b) (ha x hx)
  have he : f x-quadraticScalarSourceTwo a (scalarConstantSourceQuadraticTwo b) x =
      (f x-b)-(quadraticScalarSourceTwo a (scalarConstantSourceQuadraticTwo b) x-b) := by ring
  rw [he]
  exact (abs_sub _ _).trans ((add_le_add (hf x hx) hq).trans_eq (by ring))

end PowerConvexity
