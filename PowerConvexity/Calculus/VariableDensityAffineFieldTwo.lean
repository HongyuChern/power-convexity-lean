import PowerConvexity.Calculus.VariableDensityDirectionalGradientTwo
import PowerConvexity.Calculus.AffineBoundaryQuadraticTangencyTwo

/-! # Affine holomorphic first variation with the actual density source -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open Set Matrix
open scoped ContDiff Topology ComplexOrder BigOperators
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem affine_complex_field_variable_density_trace_two
    {U : Set E} (hU : IsOpen U) {u f : E → ℝ} (hu : ContDiffOn ℝ 3 u U)
    (hfden : ContDiffOn ℝ 1 f U) (a b : Fin 2 → E)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = (f y : ℂ))
    (hfne : ∀ y ∈ U, f y ≠ 0)
    (K : E →L[ℝ] E) (c : E) (Q : Matrix (Fin 2) (Fin 2) ℂ)
    (hKa : ∀ i, K (a i) = complexFrameReal Q a b i)
    (hKb : ∀ i, K (b i) = complexFrameImag Q a b i)
    {x : E} (hx : x ∈ U) :
    complexHessianContraction a b (complexHessian a b u x)⁻¹
      (realHessian (fun y => fderiv ℝ u y (c+K y)) x) = fderiv ℝ f x (c+K x)/f x+2*Q.trace.re := by
  have hux := hu.contDiffAt (hU.mem_nhds hx)
  have hdu := hux.fderiv_right (m := 2) (by norm_num)
  have hf : ContDiffAt ℝ 2 (fun y => fderiv ℝ u y (c+K y)) x :=
    hdu.clm_apply (contDiffAt_const.add K.contDiff.contDiffAt)
  have hg : ContDiffAt ℝ 2 (fun y => fderiv ℝ u y (c+K x)) x :=
    hdu.clm_apply contDiffAt_const
  let A := complexHessian a b u x
  have hA : IsUnit A.det := by
    rw [show A.det = (f x : ℂ) from hdet x hx]
    exact isUnit_iff_ne_zero.mpr (Complex.ofReal_ne_zero.mpr (hfne x hx))
  have hgL := directionalDerivative_variable_density_two hU hu hfden a b hdet hfne hx (c+K x)
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


variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]

theorem complex_affine_field_variable_density_two
    (e : Module.Basis (Fin 2) ℂ E) (K : E →L[ℂ] E) (c : E)
    (htrace : (complexFieldMatrixTwo e K).trace.re = 0)
    {U : Set E} (hU : IsOpen U) {u f : E → ℝ} (hu : ContDiffOn ℝ 3 u U)
    (hf : ContDiffOn ℝ 1 f U)
    (hdet : ∀ y ∈ U, (complexHessian e (fun j => Complex.I • e j) u y).det = (f y : ℂ))
    (hfne : ∀ y ∈ U, f y ≠ 0) {x : E} (hx : x ∈ U) :
    linearizedCMAOperatorTwo e (fun j => Complex.I • e j) u
      (fun y => fderiv ℝ u y (c+K y)) x = fderiv ℝ f x (c+K x)/f x := by
  obtain ⟨ha,hb⟩ := complexFieldMatrixTwo_frame e K
  have hh := affine_complex_field_variable_density_trace_two hU hu hf e (fun j => Complex.I • e j)
    hdet hfne (K.restrictScalars ℝ) c (complexFieldMatrixTwo e K) ha hb hx
  rw [htrace,mul_zero,add_zero] at hh
  exact hh

end PowerConvexity
