import PowerConvexity.Analysis.ActualFlatResidualHolderFour
import PowerConvexity.Analysis.ActualFlatEllipticCompactnessFour

/-! # Removing the constant source while preserving the actual flat boundary -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
local notation "Mat" => Matrix (Fin (2+2)) (Fin (2+2)) ℝ
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

def actualFlatSourceQuadraticFour (N : E) (b : ℝ) (x : E) : ℝ :=
  0+(0 : E →L[ℝ] ℝ) x+((-b/2) • realRankOneForm N) x x

theorem actualFlatSourceQuadraticFour_formula (N : E) (b : ℝ) (x : E) :
    actualFlatSourceQuadraticFour N b x = (-b/2)*(inner ℝ N x)^2 := by
  change 0+0+(-b/2)*(inner ℝ N x*inner ℝ N x)=_
  ring

theorem actualFlatSourceQuadraticFour_symmetric (N : E) (b : ℝ) :
    ∀ v w : E, ((-b/2) • realRankOneForm N) v w = ((-b/2) • realRankOneForm N) w v := by
  intro v w
  change (-b/2)*(inner ℝ N v*inner ℝ N w)=(-b/2)*(inner ℝ N w*inner ℝ N v)
  ring

theorem actualFlatSourceQuadraticFour_quadratic (N : E) (b : ℝ) :
    IsQuadraticPolynomial (actualFlatSourceQuadraticFour N b) :=
  ⟨0,0,(-b/2) • realRankOneForm N,actualFlatSourceQuadraticFour_symmetric N b,fun _ => rfl⟩

theorem actualFlatSourceQuadraticFour_zero (N : E) (b : ℝ) {x : E}
    (hx : inner ℝ N x=0) : actualFlatSourceQuadraticFour N b x=0 := by
  rw [actualFlatSourceQuadraticFour_formula,hx,zero_pow (by norm_num : 2 ≠ 0),mul_zero]

theorem actualFlatSourceQuadraticFour_hessian (N : E) (b : ℝ) (x : E) :
    realHessian (actualFlatSourceQuadraticFour N b) x = (-b) • realRankOneForm N := by
  rw [show actualFlatSourceQuadraticFour N b =
    (fun y => 0+(0 : E →L[ℝ] ℝ) y+((-b/2) • realRankOneForm N) y y) from rfl,
    quadratic_coeff_realHessian 0 0 _ (actualFlatSourceQuadraticFour_symmetric N b),smul_smul]
  congr 1
  ring

theorem actualFlatSourceQuadraticFour_fderiv_zero (N : E) (b : ℝ) :
    fderiv ℝ (actualFlatSourceQuadraticFour N b) 0=0 := by
  rw [show actualFlatSourceQuadraticFour N b =
    (fun y => 0+(0 : E →L[ℝ] ℝ) y+((-b/2) • realRankOneForm N) y y) from rfl,
    (quadratic_coeff_hasFDerivAt 0 0 _ (actualFlatSourceQuadraticFour_symmetric N b) 0).fderiv]
  simp only [map_zero,smul_zero,add_zero]

theorem actualFlatSourceQuadraticFour_hessian_norm {N : E} (hN : ‖N‖=1) (b : ℝ) (x : E) :
    ‖realHessian (actualFlatSourceQuadraticFour N b) x‖ = |b| := by
  rw [actualFlatSourceQuadraticFour_hessian,norm_smul,Real.norm_eq_abs,abs_neg,
    realRankOneForm,ContinuousLinearMap.norm_smulRight_apply]
  simp only [innerSL_apply_norm,hN,mul_one]

theorem actualFlatSourceQuadraticFour_source (N : E) (b : ℝ) (A : E → Mat) (x : E) :
    quadraticScalarSourceTwo A (actualFlatSourceQuadraticFour N b) x =
      b*inner ℝ N (matMulE (A x) N) := by
  have hq := (IsQuadraticPolynomial_contDiff (actualFlatSourceQuadraticFour_quadratic N b) 2).contDiffAt (x := x)
  rw [quadraticScalarSourceTwo,← actual_matrix_contraction_euclideanHessian_four (A x) hq,
    actualFlatSourceQuadraticFour_hessian,map_smul,
    actual_matrix_contraction_rankOne_energy_four,smul_eq_mul]
  ring

theorem actualFlatSourceQuadraticFour_source_identity {N : E} (hN : ‖N‖=1) (b : ℝ) (x : E) :
    quadraticScalarSourceTwo (fun _ => (1 : Mat)) (actualFlatSourceQuadraticFour N b) x=b := by
  rw [actualFlatSourceQuadraticFour_source]
  have he : matMulE (1 : Mat) N=N := by ext i; simp only [matMulE_apply,Matrix.one_mulVec]
  rw [he,real_inner_self_eq_norm_sq,hN,one_pow,mul_one]

theorem actualFlatSourceQuadraticFour_value_bound {N : E} (hN : ‖N‖=1) (b : ℝ) (x : E) :
    |actualFlatSourceQuadraticFour N b x| ≤ (|b|/2)*‖x‖^2 := by
  have hi : |inner ℝ N x| ≤ ‖x‖ := by simpa only [hN,one_mul] using abs_real_inner_le_norm N x
  have hs : (inner ℝ N x)^2 ≤ ‖x‖^2 := by nlinarith [sq_abs (inner ℝ N x),abs_nonneg (inner ℝ N x),norm_nonneg x]
  rw [actualFlatSourceQuadraticFour_formula,abs_mul,abs_div,abs_neg,
    abs_of_nonneg (sq_nonneg (inner ℝ N x))]
  rw [abs_of_pos (by norm_num : (0 : ℝ)<2)]
  exact mul_le_mul_of_nonneg_left hs (by positivity)

theorem actual_flat_constant_source_correction_error_four {N : E} (hN : ‖N‖=1)
    (A : E → Mat) (b : ℝ) (x : E) :
    |quadraticScalarSourceTwo A (actualFlatSourceQuadraticFour N b) x-b| ≤
      16*‖actualMatrixOperatorTwo (A x)-actualMatrixOperatorTwo (1 : Mat)‖*|b| := by
  have hh := actual_quadratic_source_difference_bound_four (actualFlatSourceQuadraticFour_quadratic N b)
    (abs_nonneg b) (actualFlatSourceQuadraticFour_hessian_norm hN b 0).le (A x) 1 x x
  rw [actualFlatSourceQuadraticFour_source_identity hN] at hh
  change |quadraticScalarSourceTwo A (actualFlatSourceQuadraticFour N b) x-b| ≤ _ at hh
  exact hh

end PowerConvexity
