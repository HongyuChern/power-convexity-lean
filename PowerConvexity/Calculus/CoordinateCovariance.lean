import PowerConvexity.Algebra.Congruence
import CHS.Calculus.ComplexFrame
import CHS.Calculus.AffinePullback

/-!
# Actual coordinate covariance of the modified Hessians

The convention is `∂' = Q ∂`.  For a coordinate substitution `z = P w`,
the corresponding matrix is `Q = P.transpose`.  All the objects below are
actual derivatives of the same potential.  The determinant changes by
`normSq (det Q)`; an arbitrary normalization does not preserve density one.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff BigOperators ComplexOrder

namespace PowerConvexity

open CHS.Calculus

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem complexGradient_complexFrame (Q : Matrix ι ι ℂ) (a b : ι → E)
    (u : E → ℝ) (x : E) :
    complexGradient (complexFrameReal Q a b) (complexFrameImag Q a b) u x =
      Q.mulVec (complexGradient a b u x) := by
  funext i
  exact dz_complexFrame Q a b (fun y => (u y : ℂ)) x i

theorem modifiedA_complexFrame {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hx : u x < 0)
    (Q : Matrix ι ι ℂ) (a b : ι → E) :
    modifiedA (complexFrameReal Q a b) (complexFrameImag Q a b) u x =
      Q * modifiedA a b u x * Q.conjTranspose := by
  have h := complexHessian_complexFrame (powerTransform_contDiffAt hu hx) Q a b
  rw [power_mixed_matrix hu hx, power_mixed_matrix hu hx,
    Matrix.mul_smul, Matrix.smul_mul] at h
  have hc : (sqrtSlope (u x) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (sqrtSlope_pos hx))
  ext i j
  apply mul_left_cancel₀ hc
  exact congrArg (fun M : Matrix ι ι ℂ => M i j) h

theorem modifiedB_complexFrame {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hx : u x < 0)
    (Q : Matrix ι ι ℂ) (a b : ι → E) :
    modifiedB (complexFrameReal Q a b) (complexFrameImag Q a b) u x =
      Q * modifiedB a b u x * Q.transpose := by
  have h := pureHessian_complexFrame (powerTransform_contDiffAt hu hx) Q a b
  rw [power_pure_matrix hu hx, power_pure_matrix hu hx,
    Matrix.mul_smul, Matrix.smul_mul] at h
  have hc : (sqrtSlope (u x) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (sqrtSlope_pos hx))
  ext i j
  apply mul_left_cancel₀ hc
  exact congrArg (fun M : Matrix ι ι ℂ => M i j) h

theorem modifiedSchur_complexFrame {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hx : u x < 0)
    (Q : Matrix ι ι ℂ) (hQ : IsUnit Q.det) (a b : ι → E) :
    modifiedSchur (complexFrameReal Q a b) (complexFrameImag Q a b) u x =
      Q * modifiedSchur a b u x * Q.conjTranspose := by
  unfold modifiedSchur
  rw [modifiedA_complexFrame hu hx, modifiedB_complexFrame hu hx]
  exact matrixSchur_complex_congruence Q _ _ hQ

/-- The non-Hermitian Schur quotient transforms by similarity, not congruence. -/
theorem modifiedSchur_quotient_complexFrame {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hx : u x < 0)
    (Q : Matrix ι ι ℂ) (hQ : IsUnit Q.det) (a b : ι → E) :
    modifiedSchur (complexFrameReal Q a b) (complexFrameImag Q a b) u x *
        (modifiedA (complexFrameReal Q a b) (complexFrameImag Q a b) u x)⁻¹ =
      Q * (modifiedSchur a b u x * (modifiedA a b u x)⁻¹) * Q⁻¹ := by
  rw [modifiedSchur_complexFrame hu hx Q hQ,
    modifiedA_complexFrame hu hx Q]
  exact congruence_quotient_similarity Q _ _ hQ

theorem complexHessian_det_complexFrame {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (Q : Matrix ι ι ℂ) (a b : ι → E) :
    (complexHessian (complexFrameReal Q a b) (complexFrameImag Q a b) u x).det =
      (Complex.normSq Q.det : ℂ) * (complexHessian a b u x).det := by
  rw [complexHessian_complexFrame hu]
  exact determinant_complex_congruence Q _

/-- Constant density is transferred with its actual determinant factor. -/
theorem constantDensity_complexFrame {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U)
    (Q : Matrix ι ι ℂ) (a b : ι → E) (ρ : ℂ)
    (hρ : ∀ x ∈ U, (complexHessian a b u x).det = ρ) :
    ∀ x ∈ U,
      (complexHessian (complexFrameReal Q a b) (complexFrameImag Q a b) u x).det =
        (Complex.normSq Q.det : ℂ) * ρ := by
  intro x hx
  rw [complexHessian_det_complexFrame (hu.contDiffAt (hU.mem_nhds hx)), hρ x hx]

theorem transformedDensity_ne_zero (Q : Matrix ι ι ℂ)
    (hQ : IsUnit Q.det) {ρ : ℂ} (hρ : ρ ≠ 0) :
    (Complex.normSq Q.det : ℂ) * ρ ≠ 0 := by
  apply mul_ne_zero _ hρ
  apply Complex.ofReal_ne_zero.mpr
  exact mt Complex.normSq_eq_zero.mp (isUnit_iff_ne_zero.mp hQ)

theorem complexHessian_posDef_complexFrame_iff {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (Q : Matrix ι ι ℂ)
    (hQ : IsUnit Q.det) (a b : ι → E) :
    (complexHessian (complexFrameReal Q a b) (complexFrameImag Q a b) u x).PosDef ↔
      (complexHessian a b u x).PosDef := by
  rw [complexHessian_complexFrame hu]
  exact posDef_complex_congruence_iff Q _ hQ

theorem modifiedSchur_posDef_complexFrame_iff {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hx : u x < 0)
    (Q : Matrix ι ι ℂ) (hQ : IsUnit Q.det) (a b : ι → E) :
    (modifiedSchur (complexFrameReal Q a b) (complexFrameImag Q a b) u x).PosDef ↔
      (modifiedSchur a b u x).PosDef := by
  rw [modifiedSchur_complexFrame hu hx Q hQ]
  exact posDef_complex_congruence_iff Q _ hQ

/-- An affine pullback takes the gradient in the pushed-forward directions. -/
theorem complexGradient_comp_affine {u : F → ℝ} (T : E →L[ℝ] F) (c : F) {x : E}
    (hu : DifferentiableAt ℝ u (c + T x)) (a b : ι → E) :
    complexGradient a b (fun y => u (c + T y)) x =
      complexGradient (fun i => T (a i)) (fun i => T (b i)) u (c + T x) := by
  have hf := hu.hasFDerivAt.comp x (T.hasFDerivAt.const_add c)
  change HasFDerivAt (fun y => u (c + T y))
    ((fderiv ℝ u (c + T x)).comp T) x at hf
  funext i
  rw [complexGradient_real_entry hf.differentiableAt,
    complexGradient_real_entry hu, hf.fderiv]
  rfl

theorem modifiedA_comp_affine {u : F → ℝ} (T : E →L[ℝ] F) (c : F) {x : E}
    (hu : ContDiffAt ℝ 2 u (c + T x)) (a b : ι → E) :
    modifiedA a b (fun y => u (c + T y)) x =
      modifiedA (fun i => T (a i)) (fun i => T (b i)) u (c + T x) := by
  unfold modifiedA
  rw [complexHessian_comp_affine T c hu,
    complexGradient_comp_affine T c (hu.differentiableAt (by norm_num))]

theorem modifiedB_comp_affine {u : F → ℝ} (T : E →L[ℝ] F) (c : F) {x : E}
    (hu : ContDiffAt ℝ 2 u (c + T x)) (a b : ι → E) :
    modifiedB a b (fun y => u (c + T y)) x =
      modifiedB (fun i => T (a i)) (fun i => T (b i)) u (c + T x) := by
  unfold modifiedB
  rw [pureHessian_comp_affine T c hu,
    complexGradient_comp_affine T c (hu.differentiableAt (by norm_num))]

theorem modifiedSchur_comp_affine {u : F → ℝ} (T : E →L[ℝ] F) (c : F) {x : E}
    (hu : ContDiffAt ℝ 2 u (c + T x)) (a b : ι → E) :
    modifiedSchur a b (fun y => u (c + T y)) x =
      modifiedSchur (fun i => T (a i)) (fun i => T (b i)) u (c + T x) := by
  unfold modifiedSchur
  rw [modifiedA_comp_affine T c hu, modifiedB_comp_affine T c hu]

end PowerConvexity
