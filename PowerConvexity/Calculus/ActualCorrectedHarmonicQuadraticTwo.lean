import PowerConvexity.Calculus.ActualQuadraticDeterminantBoundsTwo
import PowerConvexity.Calculus.QuadraticJointJets

/-! # Actual constant-determinant correction of the harmonic approximating polynomial.
The correction is the explicit scalar times the actual squared Euclidean norm.
Its positive branch, global actual Hessian bound and pointwise value error are
proved from the original polynomial's actual small Hessian and zero real trace.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Matrix
open scoped ContDiff Topology ComplexOrder BigOperators
namespace PowerConvexity
open CHS.Calculus CHS.Analysis CHS.Algebra
local notation "E" => DeGiorgi.AmbientSpace (2+2)
local notation "W" => Matrix (Fin 2) (Fin 2) ℂ
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem norm_sq_isQuadraticPolynomial_four : IsQuadraticPolynomial (fun x : E => ‖x‖^2) := by
  refine ⟨0,0,(1/2 : ℝ) • realHessian (fun x : E => ‖x‖^2) 0,?_,?_⟩
  · intro v w
    simp only [_root_.smul_apply,smul_eq_mul,realHessian_norm_square]
    rw [real_inner_comm v w]
  · intro x
    simp only [ContinuousLinearMap.zero_apply,zero_add,_root_.smul_apply,smul_eq_mul,
      realHessian_norm_square,real_inner_self_eq_norm_sq]
    ring

theorem actual_norm_square_Hessian_norm_le_two_four (x : E) :
    ‖realHessian (fun y : E => ‖y‖^2) x‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro v
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  rw [realHessian_norm_square,norm_mul]
  norm_num only [Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<2)]
  have hh : |inner ℝ v w| ≤ ‖v‖*‖w‖ := by
    simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) v w
  nlinarith only [hh]

theorem quadratic_complexHessian_from_zero_two {q : E → ℝ}
    (hq : IsQuadraticPolynomial q) (x : E) :
    complexHessian realDirections imagDirections q x = complexHessian realDirections imagDirections q 0 := by
  have hC := IsQuadraticPolynomial_contDiff hq 2
  ext i j
  rw [complexHessian_real_entry hC.contDiffAt,complexHessian_real_entry hC.contDiffAt]
  simp only [quadratic_realHessian_from_jet_zero hq]

def correctedHarmonicQuadraticTwo (q : E → ℝ) (x : E) : ℝ :=
  q x+tracelessDeterminantCorrectionTwo (complexHessian realDirections imagDirections q 0)*‖x‖^2

theorem correctedHarmonicQuadraticTwo_isQuadratic {q : E → ℝ} (hq : IsQuadraticPolynomial q) :
    IsQuadraticPolynomial (correctedHarmonicQuadraticTwo q) :=
  IsQuadraticPolynomial_add hq (IsQuadraticPolynomial_const_mul norm_sq_isQuadraticPolynomial_four _)

theorem correctedHarmonicQuadraticTwo_complexHessian {q : E → ℝ}
    (hq : IsQuadraticPolynomial q) (x : E) :
    complexHessian realDirections imagDirections (correctedHarmonicQuadraticTwo q) x =
      complexHessian realDirections imagDirections q 0+
      (tracelessDeterminantCorrectionTwo (complexHessian realDirections imagDirections q 0) : ℂ) • (1 : W) := by
  have hqC := IsQuadraticPolynomial_contDiff hq 2
  have hab : Orthonormal ℝ (Sum.elim (realDirections (n := 2)) imagDirections) := by
    apply orthonormal_iff_ite.mpr
    intro i j
    rw [blockDirection_eq_single,blockDirection_eq_single,
      orthonormal_iff_ite.mp (EuclideanSpace.orthonormal_single (𝕜 := ℝ))]
    simp only [Equiv.apply_eq_iff_eq]
  change complexHessian realDirections imagDirections
    (fun y => q y+tracelessDeterminantCorrectionTwo (complexHessian realDirections imagDirections q 0)*‖y‖^2) x = _
  rw [complexHessian_add_at hqC.contDiffAt
    (contDiffAt_const.mul (contDiff_norm_sq ℝ).contDiffAt),
    complexHessian_const_mul_at (contDiff_norm_sq ℝ).contDiffAt,
    norm_square_complexHessian realDirections imagDirections hab,quadratic_complexHessian_from_zero_two hq]

theorem actual_corrected_harmonic_quadratic_properties_two {q : E → ℝ} {K : ℝ}
    (hq : IsQuadraticPolynomial q) (hK : 0 ≤ K) (hK1 : K ≤ 1)
    (hH : ‖realHessian q 0‖ ≤ K)
    (ht : (realBlockHessian realDirections imagDirections q 0).trace = 0) :
    IsQuadraticPolynomial (correctedHarmonicQuadraticTwo q) ∧
      (∀ x, (1+complexHessian realDirections imagDirections (correctedHarmonicQuadraticTwo q) x).PosDef) ∧
      (∀ x, (1+complexHessian realDirections imagDirections (correctedHarmonicQuadraticTwo q) x).det = 1) ∧
      (∀ x, ‖realHessian (correctedHarmonicQuadraticTwo q) x‖ ≤ K+6*K^2) ∧
      ∀ x, |correctedHarmonicQuadraticTwo q x-q x| ≤ 3*K^2*‖x‖^2 := by
  let A := complexHessian realDirections imagDirections q 0
  let δ := tracelessDeterminantCorrectionTwo A
  have hC := IsQuadraticPolynomial_contDiff hq 2
  have hA : A.IsHermitian := complexHessian_isHermitian hC.contDiffAt realDirections imagDirections
  have hAt : A.trace = 0 := actual_complexHessian_trace_zero_of_real_trace_two hC.contDiffAt ht
  have hδ0 : 0 ≤ δ := (tracelessDeterminantCorrectionTwo_bounds hA hAt).1
  have hδ : δ ≤ 3*K^2 := (tracelessDeterminantCorrectionTwo_bounds hA hAt).2.1.trans
    (actual_complexHessian_traceless_det_bound_two hC.contDiffAt hK hH ht)
  have hpos : (1+A).PosDef := actual_small_Hessian_identity_complex_posDef_two hC.contDiffAt hH hK1
  refine ⟨correctedHarmonicQuadraticTwo_isQuadratic hq,?_,?_,?_,?_⟩
  · intro x
    rw [correctedHarmonicQuadraticTwo_complexHessian hq,← add_assoc]
    exact tracelessDeterminantCorrectionTwo_posDef hA hAt hpos
  · intro x
    rw [correctedHarmonicQuadraticTwo_complexHessian hq,← add_assoc]
    exact tracelessDeterminantCorrectionTwo_det_one hA hAt
  · intro x
    have he : realHessian (correctedHarmonicQuadraticTwo q) x =
        realHessian q x+δ • realHessian (fun y : E => ‖y‖^2) x := by
      change realHessian (fun y => q y+δ*‖y‖^2) x = _
      rw [realHessian_add hC.contDiffAt
        (contDiffAt_const.mul (contDiff_norm_sq ℝ).contDiffAt),CHS.Calculus.realHessian_const_mul]
    rw [he]
    calc
      _ ≤ ‖realHessian q x‖+‖δ • realHessian (fun y : E => ‖y‖^2) x‖ := norm_add_le (realHessian q x) (δ • realHessian (fun y : E => ‖y‖^2) x)
      _ = ‖realHessian q 0‖+δ*‖realHessian (fun y : E => ‖y‖^2) x‖ := by
        rw [quadratic_realHessian_from_jet_zero hq,norm_smul,Real.norm_eq_abs,abs_of_nonneg hδ0]
      _ ≤ K+δ*2 := add_le_add hH (mul_le_mul_of_nonneg_left (actual_norm_square_Hessian_norm_le_two_four x) hδ0)
      _ ≤ K+6*K^2 := by nlinarith only [hδ]
  · intro x
    change |q x+δ*‖x‖^2-q x| ≤ 3*K^2*‖x‖^2
    rw [add_sub_cancel_left,abs_mul,abs_of_nonneg hδ0,abs_of_nonneg (sq_nonneg ‖x‖)]
    exact mul_le_mul_of_nonneg_right hδ (sq_nonneg ‖x‖)

end PowerConvexity
