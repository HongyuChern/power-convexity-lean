import PowerConvexity.Calculus.ActualCorrectedHarmonicQuadraticTwo
import CHS.Calculus.ComplexAffineEquiv

/-! # Actual quadratic and Hessian bounds under linear pullback.
This module also derives the half-identity Hermitian lower bound directly
from the actual real Hessian, for the later uniform normalizer interface.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Matrix
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis CHS.Algebra
local notation "E" => DeGiorgi.AmbientSpace (2+2)
local notation "W" => Matrix (Fin 2) (Fin 2) ℂ
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem IsQuadraticPolynomial_comp_linear {V Z : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {q : Z → ℝ} (hq : IsQuadraticPolynomial q) (T : V →L[ℝ] Z) :
    IsQuadraticPolynomial (fun x => q (T x)) := by
  obtain ⟨c,l,H,hs,he⟩ := hq
  exact ⟨c,l.comp T,H.bilinearComp T T,fun v w => hs (T v) (T w),fun x => he (T x)⟩

theorem actual_realHessian_linear_pullback_norm_bound_two {q : E → ℝ} {x : E}
    (T : E →L[ℝ] E) (hq : ContDiffAt ℝ 2 q (T x)) {K L : ℝ}
    (hK : 0 ≤ K) (hL : 0 ≤ L) (hH : ‖realHessian q (T x)‖ ≤ K) (hT : ‖T‖ ≤ L) :
    ‖realHessian (fun y => q (T y)) x‖ ≤ K*L^2 := by
  have he (v w : E) : realHessian (fun y => q (T y)) x v w = realHessian q (T x) (T v) (T w) := by
    simpa only [zero_add] using realHessian_comp_affine T (0 : E)
      (by simpa only [zero_add] using hq) v w
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  rw [he]
  have hv : ‖T v‖ ≤ L*‖v‖ := (T.le_opNorm v).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg v))
  have hw : ‖T w‖ ≤ L*‖w‖ := (T.le_opNorm w).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg w))
  calc
    _ ≤ ‖realHessian q (T x)‖*‖T v‖*‖T w‖ := (realHessian q (T x)).le_opNorm₂ _ _
    _ ≤ K*(L*‖v‖)*(L*‖w‖) := mul_le_mul
      (mul_le_mul hH hv (norm_nonneg _) hK) hw (norm_nonneg _) (by positivity)
    _ = K*L^2*‖v‖*‖w‖ := by ring

theorem actual_small_realHessian_complex_half_lower_two {q : E → ℝ} {x : E}
    (hq : ContDiffAt ℝ 2 q x) (hH : ‖realHessian q x‖ ≤ 1) :
    ((1+complexHessian realDirections imagDirections q x)-(1/2 : ℂ) • (1 : W)).PosSemidef := by
  have hlow (v : E) : -(1*‖v‖^2) ≤ realHessian q x v v := by
    have hh := (realHessian q x).le_opNorm₂ v v
    have hb : ‖realHessian q x v v‖ ≤ 1*‖v‖^2 := hh.trans (by
      nlinarith only [mul_le_mul_of_nonneg_right hH (sq_nonneg ‖v‖)])
    exact (abs_le.mp (by simpa only [Real.norm_eq_abs] using hb)).1
  have hp := complexProjection_posSemidef (realBlockHessian_scalar_lower_posSemidef_two hq hlow)
  rw [complexProjection_add_two,complexProjection_smul,complexProjection_one_two,
    complexProjection_realBlockHessian hq,smul_smul] at hp
  convert hp using 1 <;> ext i j <;>
    simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,Complex.real_smul,smul_eq_mul,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] <;> ring

end PowerConvexity
