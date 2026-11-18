import PowerConvexity.Calculus.QuantitativeComplexAffineMapTwo
import PowerConvexity.Calculus.QuadraticAffineNormBoundsTwo

/-! # Exact actual jets under complex normalization and real dilation.
The square scaling cancels in the actual Hessian, using the locked
affine derivative theorem. The inverse pullback is an actual function identity.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Matrix
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
local notation "E" => DeGiorgi.AmbientSpace (2+2)
local notation "W" => Matrix (Fin 2) (Fin 2) ℂ
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

def complexScaledPullbackTwo (G : W) (r : ℝ) (w : E → ℝ) (x : E) : ℝ :=
  (r^2)⁻¹*w (r • complexMatrixRealMap G x)

theorem complexScaledPullbackTwo_isQuadratic {q : E → ℝ}
    (hq : IsQuadraticPolynomial q) (G : W) (r : ℝ) :
    IsQuadraticPolynomial (complexScaledPullbackTwo G r q) :=
  IsQuadraticPolynomial_const_mul
    (IsQuadraticPolynomial_comp_linear hq (r • complexMatrixRealMap G)) (r^2)⁻¹

theorem complexScaledPullbackTwo_complexHessian {G : W} {r : ℝ}
    (hr : 0 < r) {w : E → ℝ} {x : E}
    (hw : ContDiffAt ℝ 2 w (r • complexMatrixRealMap G x)) :
    complexHessian realDirections imagDirections (complexScaledPullbackTwo G r w) x =
      G.transpose*complexHessian realDirections imagDirections w
        (r • complexMatrixRealMap G x)*G.map star := by
  change complexHessian realDirections imagDirections
    (fun y => (r^2)⁻¹*w (r • complexMatrixRealMap G y)) x = _
  have hh := complexHessian_normalized_complex_affine G (0 : E) (sq_pos_of_pos hr)
    (by simpa only [Real.sqrt_sq hr.le,zero_add] using hw)
  simpa only [Real.sqrt_sq hr.le,zero_add,sub_eq_add_neg,complexHessian_add_const,
    complexScaledPullbackTwo] using hh

theorem complexScaledPullbackTwo_realHessian {G : W} {r : ℝ}
    (hr : 0 < r) {w : E → ℝ} {x : E}
    (hw : ContDiffAt ℝ 2 w (r • complexMatrixRealMap G x)) (v z : E) :
    realHessian (complexScaledPullbackTwo G r w) x v z =
      realHessian w (r • complexMatrixRealMap G x)
        (complexMatrixRealMap G v) (complexMatrixRealMap G z) := by
  change realHessian (fun y => (r^2)⁻¹*w (r • complexMatrixRealMap G y)) x v z = _
  have hh := realHessian_normalized_affine (complexMatrixRealMap G) (0 : E)
    (sq_pos_of_pos hr) (by simpa only [Real.sqrt_sq hr.le,zero_add] using hw) v z
  simpa only [Real.sqrt_sq hr.le,zero_add,sub_eq_add_neg,realHessian_add_const,
    complexScaledPullbackTwo] using hh

theorem complexScaledPullbackTwo_realHessian_norm_bound {G : W} {r : ℝ}
    (hr : 0 < r) {w : E → ℝ} {x : E}
    (hw : ContDiffAt ℝ 2 w (r • complexMatrixRealMap G x)) {K L : ℝ}
    (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hH : ‖realHessian w (r • complexMatrixRealMap G x)‖ ≤ K)
    (hG : ‖complexMatrixRealMap G‖ ≤ L) :
    ‖realHessian (complexScaledPullbackTwo G r w) x‖ ≤ K*L^2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro z
  rw [complexScaledPullbackTwo_realHessian hr hw]
  have hv : ‖complexMatrixRealMap G v‖ ≤ L*‖v‖ :=
    ((complexMatrixRealMap G).le_opNorm v).trans (mul_le_mul_of_nonneg_right hG (norm_nonneg v))
  have hz : ‖complexMatrixRealMap G z‖ ≤ L*‖z‖ :=
    ((complexMatrixRealMap G).le_opNorm z).trans (mul_le_mul_of_nonneg_right hG (norm_nonneg z))
  calc
    _ ≤ ‖realHessian w (r • complexMatrixRealMap G x)‖*
        ‖complexMatrixRealMap G v‖*‖complexMatrixRealMap G z‖ :=
      (realHessian w (r • complexMatrixRealMap G x)).le_opNorm₂ _ _
    _ ≤ K*(L*‖v‖)*(L*‖z‖) := mul_le_mul
      (mul_le_mul hH hv (norm_nonneg _) hK) hz (norm_nonneg _) (by positivity)
    _ = K*L^2*‖v‖*‖z‖ := by ring

theorem complexScaledPullbackTwo_inverse {G : W} {r : ℝ} (hr : r ≠ 0)
    (hG : IsUnit G.det) (w : E → ℝ) (x : E) :
    complexScaledPullbackTwo G⁻¹ r⁻¹ (complexScaledPullbackTwo G r w) x = w x := by
  simp only [complexScaledPullbackTwo,map_smul,smul_smul,
    ← complexMatrixRealMap_mul,Matrix.mul_nonsing_inv _ hG,complexMatrixRealMap_one,
    mul_inv_cancel₀ hr,one_smul]
  field_simp

theorem complexScaledPullbackTwo_value_error {G : W} {r : ℝ} (hr : 0 < r)
    (w q : E → ℝ) (x : E) :
    |complexScaledPullbackTwo G r w x-complexScaledPullbackTwo G r q x| =
      (r^2)⁻¹*|w (r • complexMatrixRealMap G x)-q (r • complexMatrixRealMap G x)| := by
  rw [complexScaledPullbackTwo,complexScaledPullbackTwo,← mul_sub,abs_mul,
    abs_of_pos (inv_pos.mpr (sq_pos_of_pos hr))]

end PowerConvexity
