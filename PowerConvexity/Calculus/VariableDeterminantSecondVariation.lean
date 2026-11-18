import PowerConvexity.Calculus.MatrixInverse
import PowerConvexity.Calculus.ScalarQuotientCalculus
import CHS.Calculus.DetOneSecondVariation
import CHS.Calculus.DeterminantVariation

/-! # Actual second Jacobi variation with a nonconstant determinant

The scalar derivative terms are retained. No determinant-one identity is
applied to an auxiliary equation with a variable right-hand side.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Matrix
open scoped BigOperators ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem trace_inverse_matrixDZ_eq_det_quotient
    {G : E → Matrix ι ι ℂ} {x : E}
    (hG : MatrixDifferentiableAt G x) (hdet : (G x).det ≠ 0) (a b : E) :
    Matrix.trace ((G x)⁻¹ * matrixDZ a b G x) =
      dz a b (fun y => (G y).det) x / (G x).det := by
  have hadj : (G x).adjugate = (G x).det • (G x)⁻¹ := by
    rw [Matrix.inv_def,smul_smul,Ring.mul_inverse_cancel _ (isUnit_iff_ne_zero.mpr hdet),one_smul]
  have hd : dz a b (fun y => (G y).det) x =
      (G x).det * Matrix.trace ((G x)⁻¹ * matrixDZ a b G x) := by
    rw [dz_det_at hG a b,trace_mul_eq_reversed_sum,hadj]
    simp only [Matrix.smul_apply,smul_eq_mul,Finset.mul_sum,mul_assoc]
  apply (eq_div_iff hdet).mpr
  simpa only [mul_comm] using hd.symm

theorem trace_inverse_second_matrixDZ_variable_det
    {G : E → Matrix ι ι ℂ} {U : Set E} (hU : IsOpen U)
    (hG : ∀ i j, ContDiffOn ℝ 2 (fun y => G y i j) U)
    (hdet : ∀ y ∈ U, (G y).det ≠ 0) {x : E} (hx : x ∈ U)
    (a b c d : E) :
    Matrix.trace ((G x)⁻¹ * matrixDZ a b (matrixDZ c d G) x) =
      (dz a b (dz c d (fun y => (G y).det)) x * (G x).det -
        dz c d (fun y => (G y).det) x * dz a b (fun y => (G y).det) x) /
          ((G x).det)^2 +
      Matrix.trace ((G x)⁻¹ * matrixDZ a b G x * (G x)⁻¹ * matrixDZ c d G x) := by
  have hGx i j := (hG i j).contDiffAt (hU.mem_nhds hx)
  have hGd : MatrixDifferentiableAt G x :=
    fun i j => (hGx i j).differentiableAt (by norm_num)
  have hKd := field_inverse_differentiableAt_of_det_ne_zero hGd (hdet x hx)
  have hDd := matrixDZ_differentiableAt hGx c d
  have hscalar := field_det_contDiffAt hGx
  have hfirst : (fun y => Matrix.trace ((G y)⁻¹ * matrixDZ c d G y)) =ᶠ[𝓝 x]
      (fun y => dz c d (fun z => (G z).det) y / (G y).det) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact trace_inverse_matrixDZ_eq_det_quotient
      (fun i j => ((hG i j).contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num))
      (hdet y hy) c d
  have hd := dz_congr_nhds hfirst a b
  rw [dz_trace_at (matrix_product_differentiable hKd hDd) a b,
    matrixDZ_product a b hKd hDd,
    matrixDZ_inverse_of_det_ne_zero a b hGd (hdet x hx),
    neg_mul,Matrix.trace_add,Matrix.trace_neg,
    dz_div_at ((dz_contDiffAt_one hscalar c d).differentiableAt (by norm_num))
      (hscalar.differentiableAt (by norm_num)) (hdet x hx) a b] at hd
  linear_combination hd

theorem linearized_secondDerivative_variable_density
    {u : E → ℝ} {f : E → ℂ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : ι → E)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = f y)
    (hf : ∀ y ∈ U, f y ≠ 0) {x : E} (hx : x ∈ U) (v w s t : E) :
    (∑ p, ∑ q, (complexHessian a b u x)⁻¹ q p *
      dz (a q) (-b q) (dz (a p) (b p)
        (dz s t (dz v w (fun y => (u y : ℂ))))) x) =
      (dz s t (dz v w f) x * f x-dz v w f x * dz s t f x)/(f x)^2 +
      Matrix.trace ((complexHessian a b u x)⁻¹ *
        matrixDZ s t (complexHessian a b u) x * (complexHessian a b u x)⁻¹ *
        matrixDZ v w (complexHessian a b u) x) := by
  rw [linearized_secondDerivative_eq_trace hU hu a b hx v w s t]
  have hG : ∀ i j, ContDiffOn ℝ 2 (fun y => complexHessian a b u y i j) U := by
    intro i j y hy
    exact (complexHessian_contDiffAt_two (hu.contDiffAt (hU.mem_nhds hy)) a b i j).contDiffWithinAt
  rw [trace_inverse_second_matrixDZ_variable_det hU hG
    (fun y hy => by rw [hdet y hy]; exact hf y hy) hx s t v w]
  have h1 := dz_congr_on hU hdet v w hx
  have h2 := dz_congr_on hU hdet s t hx
  have h12 := dz_congr_on hU (fun y hy => dz_congr_on hU hdet v w hy) s t hx
  rw [h1,h2,h12,hdet x hx]

end PowerConvexity
