import PowerConvexity.Calculus.MatrixIdentities

/-!
# Actual inverse calculus on the nonsingular locus

The modified Hessian does not have determinant one.  Its inverse derivatives
must therefore be derived from nonsingularity, not from the CMA density.
-/

set_option autoImplicit false
open scoped BigOperators ContDiff Topology

namespace PowerConvexity

open CHS.Calculus CHS.SchurContractionCore

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem field_inverse_contDiffAt_of_det_ne_zero {k : WithTop ℕ∞}
    {G : E → Matrix ι ι ℂ} {x : E}
    (hG : ∀ i j, ContDiffAt ℝ k (fun y => G y i j) x)
    (hdet : (G x).det ≠ 0) (i j : ι) :
    ContDiffAt ℝ k (fun y => (G y)⁻¹ i j) x := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]
  exact ((field_det_contDiffAt hG).inv hdet).mul (field_adjugate_contDiffAt hG i j)

theorem field_inverse_differentiableAt_of_det_ne_zero
    {G : E → Matrix ι ι ℂ} {x : E}
    (hG : MatrixDifferentiableAt G x) (hdet : (G x).det ≠ 0) :
    MatrixDifferentiableAt (fun y => (G y)⁻¹) x := by
  intro i j
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]
  exact ((field_det_differentiableAt hG).inv hdet).mul
    (field_adjugate_differentiableAt hG i j)

theorem matrixDZ_inverse_of_det_ne_zero (a b : E)
    {H : E → Matrix ι ι ℂ} {x : E}
    (hH : MatrixDifferentiableAt H x) (hdet : (H x).det ≠ 0) :
    matrixDZ a b (fun y => (H y)⁻¹) x =
      -((H x)⁻¹ * matrixDZ a b H x * (H x)⁻¹) := by
  have hK := field_inverse_differentiableAt_of_det_ne_zero hH hdet
  have hnear : ∀ᶠ y in 𝓝 x, (H y).det ≠ 0 :=
    (field_det_differentiableAt hH).continuousAt.eventually_ne hdet
  have hprod : (fun y => H y * (H y)⁻¹) =ᶠ[𝓝 x] (fun _ => 1) := by
    filter_upwards [hnear] with y hy
    exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hy)
  have hd : matrixDZ a b H x * (H x)⁻¹ +
      H x * matrixDZ a b (fun y => (H y)⁻¹) x = 0 := by
    calc
      _ = matrixDZ a b (fun y => H y * (H y)⁻¹) x :=
        (matrixDZ_product a b hH hK).symm
      _ = matrixDZ a b (fun _ : E => (1 : Matrix ι ι ℂ)) x :=
        matrixDZ_congr_nhds a b hprod
      _ = 0 := matrixDZ_const a b 1 x
  exact inverse_derivative_of_product_zero (H x) (H x)⁻¹
    (matrixDZ a b H x) (matrixDZ a b (fun y => (H y)⁻¹) x)
    (Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet)) hd

end PowerConvexity
