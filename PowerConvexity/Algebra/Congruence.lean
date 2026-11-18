import PowerConvexity.Calculus.ModifiedSchur

/-! # General complex congruence and the associated Schur endomorphism

The frame convention is `∂' = Q ∂`; thus A' = Q A Q*, B' = Q B Qᵀ.
For coordinates z = P w this means Q = Pᵀ.  No unitary restriction is imposed.
-/

set_option autoImplicit false
open scoped ComplexOrder

namespace PowerConvexity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem map_star_matrix_mul (A B : Matrix ι ι ℂ) :
    (A * B).map star = A.map star * B.map star :=
  Matrix.map_mul (f := starRingEnd ℂ)

theorem map_star_conjTranspose (Q : Matrix ι ι ℂ) :
    Q.conjTranspose.map star = Q.transpose := by
  ext i j
  simp only [Matrix.map_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply, star_star]

theorem determinant_complex_congruence (Q A : Matrix ι ι ℂ) :
    (Q * A * Q.conjTranspose).det = (Complex.normSq Q.det : ℂ) * A.det := by
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]
  rw [Complex.normSq_eq_conj_mul_self]
  change Q.det * A.det * star Q.det = star Q.det * Q.det * A.det
  ring

theorem matrixSchur_complex_congruence (Q A B : Matrix ι ι ℂ)
    (hQ : IsUnit Q.det) :
    matrixSchur (Q * A * Q.conjTranspose) (Q * B * Q.transpose) =
      Q * matrixSchur A B * Q.conjTranspose := by
  have hQt : IsUnit Q.transpose.det := by simpa only [Matrix.det_transpose] using hQ
  have hQb : IsUnit (Q.map star).det := by
    change IsUnit Q.conjTranspose.transpose.det
    rw [Matrix.det_transpose, Matrix.det_conjTranspose]
    exact hQ.star
  have ht : Q.transpose * Q.transpose⁻¹ = 1 := Matrix.mul_nonsing_inv _ hQt
  have hb : (Q.map star)⁻¹ * Q.map star = 1 := Matrix.nonsing_inv_mul _ hQb
  unfold matrixSchur
  rw [map_star_matrix_mul, map_star_matrix_mul,
    map_star_matrix_mul, map_star_matrix_mul, map_star_conjTranspose]
  change Q * A * Q.conjTranspose - (Q * B * Q.transpose) *
    (Q.map star * A.map star * Q.transpose)⁻¹ *
      (Q.map star * B.map star * Q.conjTranspose) = _
  simp only [Matrix.mul_inv_rev]
  calc
    _ = Q * A * Q.conjTranspose -
        Q * B * (Q.transpose * Q.transpose⁻¹) * (A.map star)⁻¹ *
          ((Q.map star)⁻¹ * Q.map star) * B.map star * Q.conjTranspose := by noncomm_ring
    _ = _ := by rw [ht, hb]; noncomm_ring

theorem congruence_quotient_similarity (Q M A : Matrix ι ι ℂ)
    (hQ : IsUnit Q.det) :
    (Q * M * Q.conjTranspose) * (Q * A * Q.conjTranspose)⁻¹ =
      Q * (M * A⁻¹) * Q⁻¹ := by
  have hQs : IsUnit Q.conjTranspose.det := by
    rw [Matrix.det_conjTranspose]
    exact hQ.star
  have hs : Q.conjTranspose * Q.conjTranspose⁻¹ = 1 := Matrix.mul_nonsing_inv _ hQs
  simp only [Matrix.mul_inv_rev]
  calc
    _ = Q * M * (Q.conjTranspose * Q.conjTranspose⁻¹) * A⁻¹ * Q⁻¹ := by noncomm_ring
    _ = _ := by rw [hs]; noncomm_ring

theorem schur_quotient_complex_similarity (Q A B : Matrix ι ι ℂ)
    (hQ : IsUnit Q.det) :
    matrixSchur (Q * A * Q.conjTranspose) (Q * B * Q.transpose) *
        (Q * A * Q.conjTranspose)⁻¹ =
      Q * (matrixSchur A B * A⁻¹) * Q⁻¹ := by
  rw [matrixSchur_complex_congruence Q A B hQ]
  exact congruence_quotient_similarity Q (matrixSchur A B) A hQ

theorem posDef_complex_congruence_iff (Q A : Matrix ι ι ℂ)
    (hQ : IsUnit Q.det) :
    (Q * A * Q.conjTranspose).PosDef ↔ A.PosDef := by
  have h := Matrix.IsUnit.posDef_star_right_conjugate_iff (x := A)
    (Q.isUnit_iff_isUnit_det.mpr hQ)
  exact h

end PowerConvexity
