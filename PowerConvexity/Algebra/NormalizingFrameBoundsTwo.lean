import PowerConvexity.Algebra.MatrixEntryBoundsTwo
import PowerConvexity.Algebra.Congruence

/-! # Every normalizing frame has controlled entries and inverse entries

These identities avoid any assumption of a continuous Takagi choice.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace PowerConvexity

theorem normalizingFrame_gram_inverse_two (Q A : Matrix (Fin 2) (Fin 2) ℂ)
    (hQ : IsUnit Q.det) (hN : Q*A*Q.conjTranspose = 1) :
    A = Q⁻¹*(Q⁻¹).conjTranspose := by
  have hQs : IsUnit Q.conjTranspose.det := by rw [Matrix.det_conjTranspose]; exact hQ.star
  have hL := Matrix.nonsing_inv_mul Q hQ
  have hR := Matrix.mul_nonsing_inv Q.conjTranspose hQs
  calc
    A = (Q⁻¹*Q)*A*(Q.conjTranspose*Q.conjTranspose⁻¹) := by rw [hL,hR]; simp
    _ = Q⁻¹*(Q*A*Q.conjTranspose)*Q.conjTranspose⁻¹ := by noncomm_ring
    _ = Q⁻¹*Q.conjTranspose⁻¹ := by rw [hN]; simp
    _ = _ := by rw [Matrix.conjTranspose_nonsing_inv]

theorem normalizingFrame_inverse_gram_two (Q A : Matrix (Fin 2) (Fin 2) ℂ)
    (hQ : IsUnit Q.det) (hN : Q*A*Q.conjTranspose = 1) :
    Q.conjTranspose*Q = A⁻¹ := by
  have hQs : IsUnit Q.conjTranspose.det := by rw [Matrix.det_conjTranspose]; exact hQ.star
  have hR := Matrix.mul_nonsing_inv Q.conjTranspose hQs
  have hh : (Q.conjTranspose*Q)*A = 1 := by
    calc
      _ = Q.conjTranspose*(Q*A*Q.conjTranspose)*Q.conjTranspose⁻¹ := by
        calc
          _ = (Q.conjTranspose*Q)*A*(Q.conjTranspose*Q.conjTranspose⁻¹) := by rw [hR]; simp
          _ = _ := by noncomm_ring
      _ = 1 := by rw [hN]; simpa using hR
  exact (Matrix.inv_eq_left_inv hh).symm

theorem matrixEntryBoundTwo_of_gram_right {Q : Matrix (Fin 2) (Fin 2) ℂ} {B : ℝ}
    (hB : 1 ≤ B) (hG : matrixEntryBoundTwo (Q*Q.conjTranspose) B) :
    matrixEntryBoundTwo Q B := by
  have hB0 : 0 ≤ B := by linarith
  intro i j
  have ht : ‖Q i 0‖^2+‖Q i 1‖^2 = ((Q*Q.conjTranspose) i i).re := by
    rw [← Complex.normSq_eq_norm_sq,← Complex.normSq_eq_norm_sq]
    simp [Matrix.mul_apply,Fin.sum_univ_two,Matrix.conjTranspose_apply,Complex.star_def,
      Complex.normSq_apply,Complex.mul_re]
  have hb : ((Q*Q.conjTranspose) i i).re ≤ B := (Complex.re_le_norm _).trans (hG i i)
  have hBB : B ≤ B^2 := by nlinarith [mul_nonneg hB0 (sub_nonneg.mpr hB)]
  apply (sq_le_sq₀ (norm_nonneg _) hB0).mp
  fin_cases j
  · change ‖Q i 0‖^2 ≤ B^2
    nlinarith [sq_nonneg ‖Q i 1‖]
  · change ‖Q i 1‖^2 ≤ B^2
    nlinarith [sq_nonneg ‖Q i 0‖]

theorem matrixEntryBoundTwo_of_gram_left {Q : Matrix (Fin 2) (Fin 2) ℂ} {B : ℝ}
    (hB : 1 ≤ B) (hG : matrixEntryBoundTwo (Q.conjTranspose*Q) B) :
    matrixEntryBoundTwo Q B := by
  have hg : matrixEntryBoundTwo (Q.conjTranspose*Q.conjTranspose.conjTranspose) B := by simpa using hG
  have hh := matrixEntryBoundTwo_of_gram_right hB hg
  intro i j
  simpa only [Matrix.conjTranspose_apply,norm_star] using hh j i

theorem normalizingFrame_entry_bounds_two (Q A : Matrix (Fin 2) (Fin 2) ℂ)
    (hQ : IsUnit Q.det) (hN : Q*A*Q.conjTranspose = 1) {B : ℝ} (hB : 1 ≤ B)
    (hA : matrixEntryBoundTwo A B) (hiA : matrixEntryBoundTwo A⁻¹ B) :
    matrixEntryBoundTwo Q B ∧ matrixEntryBoundTwo Q⁻¹ B := by
  constructor
  · apply matrixEntryBoundTwo_of_gram_left hB
    rwa [normalizingFrame_inverse_gram_two Q A hQ hN]
  · apply matrixEntryBoundTwo_of_gram_right hB
    rwa [← normalizingFrame_gram_inverse_two Q A hQ hN]

end PowerConvexity
