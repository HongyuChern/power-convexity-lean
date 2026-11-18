import PowerConvexity.Algebra.TakagiSchurSpectrumGeneral

/-! # Spectral meaning of the non-Hermitian product in cond:BABA -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ComplexOrder
namespace PowerConvexity
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem schur_positive_product_similarity {A B : Matrix ι ι ℂ}
    (hA : A.PosDef) (hB : B.transpose = B) (hM : (matrixSchur A B).PosDef) :
    ∃ (Q : Matrix ι ι ℂ) (d : ι → ℝ), IsUnit Q.det ∧
      Q * (B * (A.map star)⁻¹ * B.map star * A⁻¹) * Q⁻¹ =
        Matrix.diagonal (fun j => (d j : ℂ)) ∧
      ∀ j, 0 ≤ d j ∧ d j < 1 := by
  obtain ⟨Q,d,hQ,hQA,hd,hQB⟩ := exists_simultaneous_takagi hA hB
  have hQM : Q * matrixSchur A B * Q.conjTranspose =
      Matrix.diagonal (fun j => ((1 - d j^2 : ℝ) : ℂ)) := by
    rw [← matrixSchur_complex_congruence Q A B hQ, hQA, hQB, matrixSchur_one_real_diagonal]
  have hp : (Matrix.diagonal (fun j => ((1 - d j^2 : ℝ) : ℂ))).PosDef := by
    rw [← hQM]
    exact (posDef_complex_congruence_iff Q _ hQ).mpr hM
  have hs := schur_quotient_complex_similarity Q A B hQ
  rw [hQA, hQB, matrixSchur_one_real_diagonal, inv_one, Matrix.mul_one] at hs
  have hAu : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  rw [matrixSchur, Matrix.sub_mul, Matrix.mul_nonsing_inv A hAu,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_nonsing_inv Q hQ] at hs
  refine ⟨Q, (fun j => d j^2), hQ, ?_, ?_⟩
  · ext i j
    have he := congrArg (fun M : Matrix ι ι ℂ => M i j) hs
    by_cases hij : i = j
    · subst j
      simp only [Matrix.diagonal_apply_eq, Matrix.sub_apply, Matrix.one_apply_eq,
        Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_pow] at he ⊢
      linear_combination he
    · simp only [Matrix.diagonal_apply_ne _ hij, Matrix.sub_apply, Matrix.one_apply_ne hij,
        sub_zero, zero_sub] at he ⊢
      linear_combination he
  · intro j
    have h := (Complex.pos_iff.mp (hp.diag_pos (i := j))).1
    simp only [Matrix.diagonal_apply_eq, Complex.ofReal_re] at h
    exact ⟨sq_nonneg _, by linarith⟩

theorem schur_positive_product_real_eigenvalue_lt_one {A B : Matrix ι ι ℂ}
    (hA : A.PosDef) (hB : B.transpose = B) (hM : (matrixSchur A B).PosDef)
    {t : ℝ}
    (ht : Module.End.HasEigenvalue (B * (A.map star)⁻¹ * B.map star * A⁻¹).toLin' (t : ℂ)) :
    0 ≤ t ∧ t < 1 := by
  obtain ⟨Q,d,hQ,hdiag,hd⟩ := schur_positive_product_similarity hA hB hM
  have hcp := (charpoly_complex_similarity Q _ hQ).symm.trans (congrArg Matrix.charpoly hdiag)
  have ht' := (hasEigenvalue_of_charpoly_eq hcp (t : ℂ)).mp ht
  obtain ⟨j,hj⟩ := (real_diagonal_hasEigenvalue_iff d t).mp ht'
  exact hj ▸ hd j

end PowerConvexity
