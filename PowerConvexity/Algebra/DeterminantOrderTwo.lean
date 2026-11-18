import PowerConvexity.Algebra.TakagiSchurSpectrumTwo

/-! # Two-dimensional determinant order for classical comparison arguments -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ComplexOrder
namespace PowerConvexity

theorem det_add_scalar_one_two (A : Matrix (Fin 2) (Fin 2) ℂ) (c : ℂ) :
    (A+c • (1 : Matrix (Fin 2) (Fin 2) ℂ)).det = A.det+c*A.trace+c^2 := by
  simp only [Matrix.det_fin_two,Matrix.trace,Matrix.diag,Fin.sum_univ_two,
    Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply_eq,
    Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0),mul_one,mul_zero,add_zero]
  ring

theorem det_re_lower_of_scalar_sub_posSemidef_two
    {A : Matrix (Fin 2) (Fin 2) ℂ} {c : ℝ} (hc : 0 ≤ c)
    (hD : (A-(c:ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)).PosSemidef) :
    c^2 ≤ A.det.re := by
  let D := A-(c:ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
  have hA : A = D+(c:ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by dsimp [D]; abel
  have ht : 0 ≤ D.trace.re := (Complex.nonneg_iff.mp hD.trace_nonneg).1
  have hd : 0 ≤ D.det.re := (Complex.nonneg_iff.mp hD.det_nonneg).1
  rw [hA,det_add_scalar_one_two]
  rw [← Complex.ofReal_pow]
  simp only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero]
  have hcD := mul_nonneg hc ht
  norm_num at *
  nlinarith

theorem det_re_strict_add_scalar_two {A : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : A.PosDef) {c : ℝ} (hc : 0 < c) :
    A.det.re < (A+(c:ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)).det.re := by
  rw [det_add_scalar_one_two]
  have ht : 0 < A.trace.re := (Complex.pos_iff.mp hA.trace_pos).1
  simp only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,← Complex.ofReal_pow]
  nlinarith [mul_pos hc ht, sq_nonneg c]

theorem det_re_mono_of_posSemidef_sub_two {A B : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : A.PosDef) (hBA : (B-A).PosSemidef) : A.det.re ≤ B.det.re := by
  obtain ⟨Q,hQ,hQA⟩ := exists_complex_normalization hA
  let D := Q*(B-A)*Q.conjTranspose
  have hD : D.PosSemidef := hBA.mul_mul_conjTranspose_same Q
  have hBQ : Q*B*Q.conjTranspose = D+1 := by
    dsimp [D]
    rw [Matrix.mul_sub,Matrix.sub_mul,hQA]
    abel
  have hl : 1 ≤ (Q*B*Q.conjTranspose).det.re := by
    rw [hBQ]
    have hsub : (D+1-(1:ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)).PosSemidef := by
      simpa using hD
    simpa using det_re_lower_of_scalar_sub_posSemidef_two (c := 1) (by norm_num) hsub
  have hn : 0 < Complex.normSq Q.det :=
    Complex.normSq_pos.mpr (isUnit_iff_ne_zero.mp hQ)
  have hdetA := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M.det.re) hQA
  rw [determinant_complex_congruence] at hdetA
  rw [determinant_complex_congruence] at hl
  simp only [Matrix.det_one,Complex.one_re,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero] at hdetA hl
  nlinarith

end PowerConvexity
