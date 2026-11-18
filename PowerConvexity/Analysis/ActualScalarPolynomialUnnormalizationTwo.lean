import PowerConvexity.Analysis.ActualScalarCorrectedNormalizationTwo

/-! # Actual polynomial and error after undoing the scalar normalization.
The same particular quadratic and amplitude restore all actual jets,
the frozen source value and the physical-ball integral error.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem scalarConstantSourceQuadraticTwo_trace (b : ℝ) (x : E) :
    (realBlockHessian realDirections imagDirections (scalarConstantSourceQuadraticTwo b) x).trace = -b := by
  have he : quadraticScalarSourceTwo (fun _ => (1 : Matrix (Fin (2+2)) (Fin (2+2)) ℝ))
      (scalarConstantSourceQuadraticTwo b) x =
      -(realBlockHessian realDirections imagDirections (scalarConstantSourceQuadraticTwo b) x).trace := by
    simp only [quadraticScalarSourceTwo,Matrix.one_apply,ite_mul,one_mul,zero_mul,
      Finset.sum_ite_eq,Finset.mem_univ,if_true,euclideanHessian,actual_euclidean_trace_eq_block_trace_two]
  have hh := scalarConstantSourceQuadraticTwo_source
    (fun _ => (1 : Matrix (Fin (2+2)) (Fin (2+2)) ℝ)) b x
  rw [he] at hh
  have htr : (1 : Matrix (Fin (2+2)) (Fin (2+2)) ℝ).trace = 4 := by norm_num [Matrix.trace]
  rw [htr] at hh
  linarith

def scalarCorrectedQuadraticTwo (b S : ℝ) (p : E → ℝ) (x : E) : ℝ :=
  scalarConstantSourceQuadraticTwo b x+S*p x

theorem actual_scalar_corrected_quadratic_properties_two {b S M : ℝ}
    {p : E → ℝ} (hp : IsQuadraticPolynomial p) (hS : 0 ≤ S)
    (hpt : ∀ x, (realBlockHessian realDirections imagDirections p x).trace = 0)
    (hp0 : |p 0| ≤ M) (hp1 : ‖fderiv ℝ p 0‖ ≤ M) (hp2 : ∀ x, ‖realHessian p x‖ ≤ M) :
    IsQuadraticPolynomial (scalarCorrectedQuadraticTwo b S p) ∧
    (∀ x, (realBlockHessian realDirections imagDirections (scalarCorrectedQuadraticTwo b S p) x).trace = -b) ∧
    |scalarCorrectedQuadraticTwo b S p 0| ≤ S*M ∧
    ‖fderiv ℝ (scalarCorrectedQuadraticTwo b S p) 0‖ ≤ S*M ∧
    ∀ x, ‖realHessian (scalarCorrectedQuadraticTwo b S p) x‖ ≤ |b|/4+S*M := by
  have hq := scalarConstantSourceQuadraticTwo_isQuadratic b
  have hqC := IsQuadraticPolynomial_contDiff hq 2
  have hpC := IsQuadraticPolynomial_contDiff hp 2
  have hH (x : E) : realHessian (scalarCorrectedQuadraticTwo b S p) x =
      realHessian (scalarConstantSourceQuadraticTwo b) x+S • realHessian p x := by
    change realHessian (fun y => scalarConstantSourceQuadraticTwo b y+S*p y) x = _
    rw [realHessian_add hqC.contDiffAt (contDiffAt_const.mul hpC.contDiffAt),realHessian_const_mul]
  refine ⟨IsQuadraticPolynomial_add hq (IsQuadraticPolynomial_const_mul hp S),?_,?_,?_,?_⟩
  · intro x
    have he : realBlockHessian realDirections imagDirections (scalarCorrectedQuadraticTwo b S p) x =
        realBlockHessian realDirections imagDirections (scalarConstantSourceQuadraticTwo b) x+
          S • realBlockHessian realDirections imagDirections p x := by
      ext i j
      simp only [realBlockHessian,hH,_root_.add_apply,_root_.smul_apply,
        smul_eq_mul,Matrix.add_apply,Matrix.smul_apply]
    rw [he,Matrix.trace_add,Matrix.trace_smul,scalarConstantSourceQuadraticTwo_trace,
      hpt x,smul_zero,add_zero]
  · simp only [scalarCorrectedQuadraticTwo,scalarConstantSourceQuadraticTwo,norm_zero,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0),mul_zero,zero_add,abs_mul,abs_of_nonneg hS]
    exact mul_le_mul_of_nonneg_left hp0 hS
  · have hqD : fderiv ℝ (scalarConstantSourceQuadraticTwo b) 0 = 0 := by
      change fderiv ℝ ((-b/8) • (fun y : E => ‖y‖^2)) 0 = 0
      rw [fderiv_const_smul_field,Pi.smul_apply,fderiv_norm_sq_apply]
      simp
    change ‖fderiv ℝ (fun y => scalarConstantSourceQuadraticTwo b y+(S • p) y) 0‖ ≤ _
    rw [fderiv_fun_add (hqC.differentiable (by norm_num)).differentiableAt
      ((hpC.differentiable (by norm_num)).const_smul S).differentiableAt,
      fderiv_const_smul_field,Pi.smul_apply,hqD,zero_add,norm_smul,Real.norm_eq_abs,abs_of_nonneg hS]
    exact mul_le_mul_of_nonneg_left hp1 hS
  · intro x
    rw [hH x]
    calc
      _ ≤ ‖realHessian (scalarConstantSourceQuadraticTwo b) x‖+‖S • realHessian p x‖ :=
        norm_add_le (realHessian (scalarConstantSourceQuadraticTwo b) x) (S • realHessian p x)
      _ = ‖realHessian (scalarConstantSourceQuadraticTwo b) x‖+S*‖realHessian p x‖ := by
        rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hS]
      _ ≤ _ := add_le_add (scalarConstantSourceQuadraticTwo_Hessian_bound b x)
        (mul_le_mul_of_nonneg_left (hp2 x) hS)

theorem actual_scalar_unnormalized_error_identity_two {b S : ℝ}
    (hS : 0 < S) (u p : E → ℝ) (U : Set E) :
    (∫ x in U, (u x-scalarCorrectedQuadraticTwo b S p x)^2) =
      S^2*(∫ x in U, (S⁻¹*(u x-scalarConstantSourceQuadraticTwo b x)-p x)^2) := by
  have he : (fun x => (u x-scalarCorrectedQuadraticTwo b S p x)^2) =
      fun x => S^2*(S⁻¹*(u x-scalarConstantSourceQuadraticTwo b x)-p x)^2 := by
    funext x
    simp only [scalarCorrectedQuadraticTwo]
    field_simp
    ring
  rw [he,integral_const_mul]

end PowerConvexity
