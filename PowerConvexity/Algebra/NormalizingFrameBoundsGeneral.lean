import PowerConvexity.Algebra.NormalizingFrameBoundsTwo

/-! # Uniform entry bounds for all normalizing frames in finite dimension -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace PowerConvexity
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem normalizingFrame_gram_inverse_general (Q A : Matrix ι ι ℂ)
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

theorem normalizingFrame_inverse_gram_general (Q A : Matrix ι ι ℂ)
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

theorem matrix_entry_bound_of_gram_right_general {Q : Matrix ι ι ℂ} {B : ℝ}
    (hB : 1 ≤ B) (hG : ∀ i j, ‖(Q*Q.conjTranspose) i j‖ ≤ B) :
    ∀ i j, ‖Q i j‖ ≤ B := by
  have hB0 : 0 ≤ B := by linarith
  intro i j
  have ht : ∑ k, ‖Q i k‖^2 = ((Q*Q.conjTranspose) i i).re := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply, Complex.mul_re, Complex.star_def]
  have hj : ‖Q i j‖^2 ≤ ∑ k, ‖Q i k‖^2 :=
    Finset.single_le_sum (fun k _ => sq_nonneg ‖Q i k‖) (Finset.mem_univ j)
  have hb : ((Q*Q.conjTranspose) i i).re ≤ B := (Complex.re_le_norm _).trans (hG i i)
  apply (sq_le_sq₀ (norm_nonneg _) hB0).mp
  rw [ht] at hj
  nlinarith

theorem matrix_entry_bound_of_gram_left_general {Q : Matrix ι ι ℂ} {B : ℝ}
    (hB : 1 ≤ B) (hG : ∀ i j, ‖(Q.conjTranspose*Q) i j‖ ≤ B) :
    ∀ i j, ‖Q i j‖ ≤ B := by
  have hg : ∀ i j, ‖(Q.conjTranspose*Q.conjTranspose.conjTranspose) i j‖ ≤ B := by simpa using hG
  have hh := matrix_entry_bound_of_gram_right_general hB hg
  intro i j
  simpa only [Matrix.conjTranspose_apply,norm_star] using hh j i

theorem normalizingFrame_entry_bounds_general (Q A : Matrix ι ι ℂ)
    (hQ : IsUnit Q.det) (hN : Q*A*Q.conjTranspose = 1) {B : ℝ} (hB : 1 ≤ B)
    (hA : ∀ i j, ‖A i j‖ ≤ B) (hiA : ∀ i j, ‖A⁻¹ i j‖ ≤ B) :
    (∀ i j, ‖Q i j‖ ≤ B) ∧ (∀ i j, ‖Q⁻¹ i j‖ ≤ B) := by
  constructor
  · apply matrix_entry_bound_of_gram_left_general hB
    rwa [normalizingFrame_inverse_gram_general Q A hQ hN]
  · apply matrix_entry_bound_of_gram_right_general hB
    rwa [← normalizingFrame_gram_inverse_general Q A hQ hN]

end PowerConvexity
