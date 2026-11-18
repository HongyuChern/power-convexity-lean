import PowerConvexity.Calculus.AffineDirectionalHessian
import PowerConvexity.Calculus.CoordinateCovariance

/-! # Actual affine complex frame fields and their linearized CMA equation

The compatibility assumptions identify the genuine real linear map K on both
blocks of the complex frame. No independent third or fourth jet is prescribed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Matrix
open scoped ContDiff Topology ComplexOrder BigOperators
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem frameReal_one_add_two (Q : Matrix (Fin 2) (Fin 2) ℂ)
    (a b : Fin 2 → E) (i : Fin 2) :
    complexFrameReal (1+Q) a b i = a i+complexFrameReal Q a b i := by
  fin_cases i <;>
    simp [complexFrameReal,Fin.sum_univ_two,Matrix.add_apply,Matrix.one_apply,
      Complex.add_re,Complex.add_im,add_smul] <;> module

private theorem frameImag_one_add_two (Q : Matrix (Fin 2) (Fin 2) ℂ)
    (a b : Fin 2 → E) (i : Fin 2) :
    complexFrameImag (1+Q) a b i = b i+complexFrameImag Q a b i := by
  fin_cases i <;>
    simp [complexFrameImag,Fin.sum_univ_two,Matrix.add_apply,Matrix.one_apply,
      Complex.add_re,Complex.add_im,add_smul] <;> module

theorem complexHessian_directional_affine_frame_two
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 3 u x)
    (K : E →L[ℝ] E) (c : E) (a b : Fin 2 → E)
    (Q : Matrix (Fin 2) (Fin 2) ℂ)
    (hKa : ∀ i, K (a i) = complexFrameReal Q a b i)
    (hKb : ∀ i, K (b i) = complexFrameImag Q a b i) :
    complexHessian a b (fun y => fderiv ℝ u y (c+K y)) x =
      complexHessian a b (fun y => fderiv ℝ u y (c+K x)) x+
        Q*complexHessian a b u x+complexHessian a b u x*Q.conjTranspose := by
  have hu2 : ContDiffAt ℝ 2 u x := hu.of_le (by norm_num)
  have hdu := hu.fderiv_right (m := 2) (by norm_num)
  have hf : ContDiffAt ℝ 2 (fun y => fderiv ℝ u y (c+K y)) x :=
    hdu.clm_apply (contDiffAt_const.add K.contDiff.contDiffAt)
  have hg : ContDiffAt ℝ 2 (fun y => fderiv ℝ u y (c+K x)) x :=
    hdu.clm_apply contDiffAt_const
  have hpol : complexHessian a b (fun y => fderiv ℝ u y (c+K y)) x =
      complexHessian a b (fun y => fderiv ℝ u y (c+K x)) x+
        complexHessian (complexFrameReal (1+Q) a b) (complexFrameImag (1+Q) a b) u x-
        complexHessian a b u x-
        complexHessian (complexFrameReal Q a b) (complexFrameImag Q a b) u x := by
    ext i j
    simp only [Matrix.add_apply,Matrix.sub_apply]
    rw [complexHessian_real_entry hf,complexHessian_real_entry hg]
    rw [realHessian_directional_affine_difference hu K c (a i) (a j),
      realHessian_directional_affine_difference hu K c (b i) (b j),
      realHessian_directional_affine_difference hu K c (a i) (b j),
      realHessian_directional_affine_difference hu K c (b i) (a j)]
    rw [realHessian_symm hu2 (a j) (K (a i)),realHessian_symm hu2 (b j) (K (b i)),
      realHessian_symm hu2 (b j) (K (a i)),realHessian_symm hu2 (a j) (K (b i))]
    simp only [complexHessian_real_entry hu2,frameReal_one_add_two,frameImag_one_add_two,
      ← hKa,← hKb,map_add,ContinuousLinearMap.add_apply,Complex.ofReal_add,Complex.ofReal_sub]
    ring
  rw [complexHessian_complexFrame hu2 (1+Q),complexHessian_complexFrame hu2 Q] at hpol
  simp only [Matrix.conjTranspose_add,Matrix.conjTranspose_one] at hpol
  rw [hpol]
  noncomm_ring


theorem affine_complex_field_linearized_trace_two
    {U : Set E} (hU : IsOpen U) {u : E → ℝ} (hu : ContDiffOn ℝ 3 u U)
    (a b : Fin 2 → E) (hdet : ∀ y ∈ U, (complexHessian a b u y).det = 1)
    (K : E →L[ℝ] E) (c : E) (Q : Matrix (Fin 2) (Fin 2) ℂ)
    (hKa : ∀ i, K (a i) = complexFrameReal Q a b i)
    (hKb : ∀ i, K (b i) = complexFrameImag Q a b i)
    {x : E} (hx : x ∈ U) :
    complexHessianContraction a b (complexHessian a b u x)⁻¹
      (realHessian (fun y => fderiv ℝ u y (c+K y)) x) = 2*Q.trace.re := by
  have hux := hu.contDiffAt (hU.mem_nhds hx)
  have hdu := hux.fderiv_right (m := 2) (by norm_num)
  have hf : ContDiffAt ℝ 2 (fun y => fderiv ℝ u y (c+K y)) x :=
    hdu.clm_apply (contDiffAt_const.add K.contDiff.contDiffAt)
  have hg : ContDiffAt ℝ 2 (fun y => fderiv ℝ u y (c+K x)) x :=
    hdu.clm_apply contDiffAt_const
  let A := complexHessian a b u x
  have hA : IsUnit A.det := by rw [show A.det = 1 from hdet x hx]; exact isUnit_one
  have hgL := directionalDerivative_contraction_zero hU hu a b hdet hx (c+K x)
  rw [← complexHessianContraction_pairing a b _ hg,complex_contraction_eq_trace hg] at hgL
  have hQ : (Q*A*A⁻¹).trace = Q.trace := by
    rw [Matrix.mul_assoc,Matrix.mul_nonsing_inv A hA,Matrix.mul_one]
  have hQt : (A*Q.conjTranspose*A⁻¹).trace = Q.conjTranspose.trace := by
    rw [Matrix.trace_mul_cycle,Matrix.nonsing_inv_mul A hA,Matrix.one_mul]
  rw [← complexHessianContraction_pairing a b _ hf,complex_contraction_eq_trace hf,
    complexHessian_directional_affine_frame_two hux K c a b Q hKa hKb,
    Matrix.add_mul,Matrix.add_mul,Matrix.trace_add,Matrix.trace_add,
    Complex.add_re,Complex.add_re]
  change _+((Q*A)*A⁻¹).trace.re+((A*Q.conjTranspose)*A⁻¹).trace.re = _
  rw [hQ,hQt,hgL]
  simp only [Matrix.trace_conjTranspose,Complex.star_def,Complex.conj_re]
  ring

end PowerConvexity
