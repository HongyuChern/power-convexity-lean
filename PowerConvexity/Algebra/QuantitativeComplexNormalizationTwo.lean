import PowerConvexity.Algebra.DimensionTwo
import CHS.Algebra.ComplexNormalization
import CHS.Calculus.ComplexAffineEquiv

/-! # Uniform entry bounds for actual determinant-one normalizers.
The lower Hermitian bound is transported by the actual normalizing matrix.
In complex dimension two its inverse is bounded by the explicit adjugate.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
open Matrix
open scoped ComplexOrder BigOperators
namespace PowerConvexity
local notation "W" => Matrix (Fin 2) (Fin 2) ℂ

theorem complex_normalizer_entry_bound_two {C G : W}
    (hC : (C-(1/2 : ℂ) • (1 : W)).PosSemidef)
    (hG : G.transpose*C*G.map star = 1) (i j : Fin 2) : ‖G i j‖ ≤ 2 := by
  have hp := hC.mul_mul_conjTranspose_same G.transpose
  have he : G.transpose*(C-(1/2 : ℂ) • (1 : W))*G.transpose.conjTranspose =
      1-(1/2 : ℂ) • (G.transpose*G.map star) := by
    change G.transpose*(C-(1/2 : ℂ) • (1 : W))*G.map star = _
    rw [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.mul_one,Matrix.smul_mul,hG]
  rw [he] at hp
  have hd := (Complex.nonneg_iff.mp (hp.diag_nonneg (i := j))).1
  have hd' : (G 0 j).re^2+(G 0 j).im^2+(G 1 j).re^2+(G 1 j).im^2 ≤ 2 := by
    simp only [Matrix.sub_apply,Matrix.one_apply_eq,Matrix.smul_apply,smul_eq_mul,
      Matrix.mul_apply,Fin.sum_univ_two,Matrix.transpose_apply,Matrix.map_apply,
      Complex.star_def,Complex.sub_re,Complex.one_re,Complex.mul_re,Complex.mul_im,
      Complex.conj_re,Complex.conj_im,Complex.add_re,Complex.add_im] at hd
    norm_num at hd
    nlinarith only [hd]
  have hs : ‖G i j‖^2 ≤ 2 := by
    rw [Complex.sq_norm,Complex.normSq_apply]
    fin_cases i
    · change (G 0 j).re*(G 0 j).re+(G 0 j).im*(G 0 j).im ≤ 2
      nlinarith only [hd',sq_nonneg (G 1 j).re,sq_nonneg (G 1 j).im]
    · change (G 1 j).re*(G 1 j).re+(G 1 j).im*(G 1 j).im ≤ 2
      nlinarith only [hd',sq_nonneg (G 0 j).re,sq_nonneg (G 0 j).im]
  nlinarith only [hs,norm_nonneg (G i j)]

theorem determinant_norm_eq_one_of_normSq_two {G : W}
    (hG : Complex.normSq G.det = 1) : ‖G.det‖ = 1 := by
  rw [Complex.normSq_eq_norm_sq] at hG
  nlinarith only [hG,norm_nonneg G.det]

theorem inverse_entry_bound_of_det_norm_one_two {G : W} {K : ℝ}
    (hG : ‖G.det‖ = 1) (hentry : ∀ i j, ‖G i j‖ ≤ K) (i j : Fin 2) :
    ‖G⁻¹ i j‖ ≤ K := by
  rw [Matrix.inv_def,Matrix.smul_apply,smul_eq_mul,norm_mul]
  have hi : ‖Ring.inverse G.det‖ = 1 := by
    rw [Ring.inverse_eq_inv,norm_inv,hG,inv_one]
  rw [hi,one_mul,Matrix.adjugate_fin_two]
  fin_cases i <;> fin_cases j
  · exact hentry 1 1
  · change ‖-(G 0 1)‖ ≤ K
    simpa only [norm_neg] using hentry 0 1
  · change ‖-(G 1 0)‖ ≤ K
    simpa only [norm_neg] using hentry 1 0
  · exact hentry 0 0

theorem exists_uniform_complex_normalizer_two {C : W} (hC : C.PosDef)
    (hdet : C.det = 1) (hlower : (C-(1/2 : ℂ) • (1 : W)).PosSemidef) :
    ∃ G : W, G.transpose*C*G.map star = 1 ∧ Complex.normSq G.det = 1 ∧
      (∀ i j, ‖G i j‖ ≤ 2) ∧ (∀ i j, ‖G⁻¹ i j‖ ≤ 2) := by
  obtain ⟨G,hG,hGdet⟩ := CHS.Algebra.exists_complex_normalization_of_det_one hC hdet
  have he := complex_normalizer_entry_bound_two hlower hG
  exact ⟨G,hG,hGdet,he,inverse_entry_bound_of_det_norm_one_two
    (determinant_norm_eq_one_of_normSq_two hGdet) he⟩

end PowerConvexity
