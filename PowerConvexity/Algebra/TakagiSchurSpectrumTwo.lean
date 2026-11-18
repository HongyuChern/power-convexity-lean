import PowerConvexity.Calculus.TakagiNormalizationTwo

/-!
# Ordered Schur roots and generalized Rayleigh bounds in dimension two

The Schur quotient itself need not be Hermitian.  Congruence of its pair
(M,A) gives the Hermitian quadratic-form comparison M >= sigma A.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ComplexOrder
namespace PowerConvexity

theorem schur_quotient_takagi_real_pair
    (A B Q : Matrix (Fin 2) (Fin 2) ℂ) (d : Fin 2 → ℝ)
    (hQ : IsUnit Q.det) (hA : Q*A*Q.conjTranspose = 1)
    (hB : Q*B*Q.transpose = Matrix.diagonal (fun i => (d i:ℂ))) :
    (matrixSchur A B * A⁻¹).charpoly =
      (Polynomial.X - Polynomial.C ((1-d 0^2:ℝ):ℂ)) *
      (Polynomial.X - Polynomial.C ((1-d 1^2:ℝ):ℂ)) := by
  have hs := schur_quotient_complex_similarity Q A B hQ
  rw [hA,hB,matrixSchur_one_real_diagonal,inv_one,Matrix.mul_one] at hs
  calc
    _ = (Q*(matrixSchur A B*A⁻¹)*Q⁻¹).charpoly :=
      (charpoly_complex_similarity Q _ hQ).symm
    _ = (Matrix.diagonal (fun i => ((1-d i^2:ℝ):ℂ))).charpoly := congrArg Matrix.charpoly hs.symm
    _ = _ := real_diagonal_charpoly_pair (fun i => 1-d i^2)

theorem schur_quotient_takagi_ordered_roots
    (A B Q : Matrix (Fin 2) (Fin 2) ℂ) (d : Fin 2 → ℝ)
    (hQ : IsUnit Q.det) (hA : Q*A*Q.conjTranspose = 1)
    (hB : Q*B*Q.transpose = Matrix.diagonal (fun i => (d i:ℂ)))
    (hd1 : 0 ≤ d 1) (hd : d 1 ≤ d 0) :
    lowerEigenvalueTwo (matrixSchur A B*A⁻¹) = 1-d 0^2 ∧
      upperEigenvalueTwo (matrixSchur A B*A⁻¹) = 1-d 1^2 := by
  have hroot := schur_quotient_takagi_real_pair A B Q d hQ hA hB
  have hord : 1-d 0^2 ≤ 1-d 1^2 := by nlinarith
  exact ⟨(lowerEigenvalueTwo_of_real_pair _ _ _ hroot).trans (min_eq_left hord),
    (upperEigenvalueTwo_of_real_pair _ _ _ hroot).trans (max_eq_right hord)⟩

/-- The exact degeneracy tested in Appendix A is equality of the two
nonnegative Takagi singular values. -/
theorem schur_quotient_gap_iff_takagi
    (A B Q : Matrix (Fin 2) (Fin 2) ℂ) (d : Fin 2 → ℝ)
    (hQ : IsUnit Q.det) (hA : Q*A*Q.conjTranspose = 1)
    (hB : Q*B*Q.transpose = Matrix.diagonal (fun i => (d i:ℂ)))
    (hd1 : 0 ≤ d 1) (hd : d 1 ≤ d 0) :
    lowerEigenvalueTwo (matrixSchur A B*A⁻¹) <
      upperEigenvalueTwo (matrixSchur A B*A⁻¹) ↔ d 1 < d 0 := by
  obtain ⟨hl,hu⟩ := schur_quotient_takagi_ordered_roots A B Q d hQ hA hB hd1 hd
  rw [hl,hu]
  constructor <;> intro h <;> nlinarith

theorem schur_takagi_upper_bound
    (A B Q : Matrix (Fin 2) (Fin 2) ℂ) (d : Fin 2 → ℝ)
    (hQ : IsUnit Q.det) (hA : Q*A*Q.conjTranspose = 1)
    (hB : Q*B*Q.transpose = Matrix.diagonal (fun i => (d i:ℂ)))
    (hd1 : 0 ≤ d 1) (hd : d 1 ≤ d 0) (hM : (matrixSchur A B).PosSemidef) :
    d 0 ≤ 1 := by
  have hc := hM.mul_mul_conjTranspose_same Q
  rw [← matrixSchur_complex_congruence Q A B hQ,hA,hB,matrixSchur_one_real_diagonal] at hc
  have he : 0 ≤ (1-d 0^2:ℝ) := by
    have hh := (Complex.nonneg_iff.mp (hc.diag_nonneg (i := 0))).1
    simpa only [Matrix.diagonal_apply_eq, Complex.ofReal_re] using hh
  nlinarith

/-- This is a form inequality for the original unnormalized matrices. -/
theorem schur_sub_lower_mul_posSemidef {A B : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : A.PosDef) (hB : B.transpose = B) :
    (matrixSchur A B - (lowerEigenvalueTwo (matrixSchur A B*A⁻¹):ℂ) • A).PosSemidef := by
  obtain ⟨Q,d,hQ,hQA,hd1,hd,hQB⟩ := exists_simultaneous_takagi_two hA hB
  let s := lowerEigenvalueTwo (matrixSchur A B*A⁻¹)
  have hs : s = 1-d 0^2 :=
    (schur_quotient_takagi_ordered_roots A B Q d hQ hQA hQB hd1 hd).1
  have hQM : Q*matrixSchur A B*Q.conjTranspose =
      Matrix.diagonal (fun i => ((1-d i^2:ℝ):ℂ)) := by
    rw [← matrixSchur_complex_congruence Q A B hQ,hQA,hQB,matrixSchur_one_real_diagonal]
  have hcong : Q*(matrixSchur A B-(s:ℂ) • A)*Q.conjTranspose =
      Matrix.diagonal (fun i => ((1-d i^2-s:ℝ):ℂ)) := by
    rw [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,hQM,hQA]
    ext i j
    by_cases hij : i=j
    · subst j
      simp [Matrix.diagonal_apply,Matrix.one_apply,Complex.ofReal_sub]
    · simp [Matrix.diagonal_apply,Matrix.one_apply,hij]
  have hpos : (Q*(matrixSchur A B-(s:ℂ) • A)*Q.conjTranspose).PosSemidef := by
    rw [hcong]
    apply Matrix.PosSemidef.diagonal
    intro i
    apply Complex.zero_le_real.mpr
    fin_cases i
    · change 0 ≤ 1-d 0^2-s
      rw [hs]
      linarith
    · change 0 ≤ 1-d 1^2-s
      rw [hs]
      nlinarith
  exact (Matrix.IsUnit.posSemidef_star_right_conjugate_iff
    (x := matrixSchur A B-(s:ℂ) • A) (Matrix.isUnit_iff_isUnit_det Q |>.mpr hQ)).mp hpos

theorem schur_lower_le_diagonal_ratio {A B : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : A.PosDef) (hB : B.transpose = B) (i : Fin 2) :
    lowerEigenvalueTwo (matrixSchur A B*A⁻¹) ≤ (matrixSchur A B i i).re / (A i i).re := by
  have h := (Complex.nonneg_iff.mp
    ((schur_sub_lower_mul_posSemidef hA hB).diag_nonneg (i := i))).1
  have hp : 0 < (A i i).re := (Complex.pos_iff.mp (hA.diag_pos (i := i))).1
  apply (le_div_iff₀ hp).mpr
  simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,Complex.sub_re,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at h
  linarith

end PowerConvexity
