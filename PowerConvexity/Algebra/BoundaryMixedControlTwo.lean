import PowerConvexity.Algebra.DeterminantOrderTwo

/-! # What determinant one does and does not control at the boundary

A positive tangential complex diagonal and a mixed-entry bound control the
normal complex diagonal. The explicit positive determinant-one family below
shows that the mixed-entry bound cannot be discarded as a purely algebraic step.
-/
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Matrix
open scoped ComplexOrder
namespace PowerConvexity

theorem hermitian_det_one_normal_diagonal_bound_two
    {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.PosDef) (hdet : A.det = 1)
    {delta M : ℝ} (hd : 0 < delta) (ha : delta ≤ (A 0 0).re)
    (hm : Complex.normSq (A 0 1) ≤ M) :
    (A 1 1).re ≤ (1+M)/delta := by
  have h00 := Complex.pos_iff.mp (hA.diag_pos (i := 0))
  have h11 := Complex.pos_iff.mp (hA.diag_pos (i := 1))
  have h10 : A 1 0 = star (A 0 1) := (hA.isHermitian.apply 1 0).symm
  have hid : (A 0 0).re*(A 1 1).re = 1+Complex.normSq (A 0 1) := by
    have hh := congrArg Complex.re hdet
    rw [Matrix.det_fin_two,h10] at hh
    simp only [Complex.sub_re,Complex.mul_re,← h00.2,← h11.2,Complex.star_def,
      Complex.conj_re,Complex.conj_im,Complex.one_re,zero_mul,sub_zero] at hh
    rw [Complex.normSq_apply]
    nlinarith
  apply (le_div_iff₀ hd).mpr
  have hh := mul_le_mul_of_nonneg_right ha h11.1.le
  nlinarith

noncomputable def boundaryMixedEscapeMatrixTwo (r : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1,(r : ℂ);(r : ℂ),1+(r : ℂ)^2]

theorem boundaryMixedEscapeMatrixTwo_det (r : ℝ) :
    (boundaryMixedEscapeMatrixTwo r).det = 1 := by
  simp [boundaryMixedEscapeMatrixTwo,Matrix.det_fin_two]
  <;> ring

theorem boundaryMixedEscapeMatrixTwo_posDef (r : ℝ) :
    (boundaryMixedEscapeMatrixTwo r).PosDef := by
  let T : Matrix (Fin 2) (Fin 2) ℂ := !![1,(r : ℂ);0,1]
  have hdet : T.det = 1 := by simp [T,Matrix.det_fin_two]
  have hinj : Function.Injective T.mulVec := Matrix.mulVec_injective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det T).mpr (by rw [hdet]; exact isUnit_one))
  have he : T.conjTranspose*T = boundaryMixedEscapeMatrixTwo r := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [T,boundaryMixedEscapeMatrixTwo,Matrix.mul_apply,Matrix.conjTranspose_apply,
        Fin.sum_univ_two] <;> ring
  rw [← he]
  exact Matrix.PosDef.conjTranspose_mul_self T hinj

theorem boundaryMixedEscapeMatrixTwo_unbounded_normal (M : ℝ) :
    ∃ A : Matrix (Fin 2) (Fin 2) ℂ,
      A.PosDef ∧ A.det = 1 ∧ A 0 0 = 1 ∧ M < (A 1 1).re := by
  let r := |M|+1
  refine ⟨boundaryMixedEscapeMatrixTwo r,boundaryMixedEscapeMatrixTwo_posDef r,
    boundaryMixedEscapeMatrixTwo_det r,by simp [boundaryMixedEscapeMatrixTwo],?_⟩
  simp only [boundaryMixedEscapeMatrixTwo,Matrix.of_apply,Matrix.cons_val_one,
    Matrix.cons_val_zero,Complex.add_re,Complex.one_re,← Complex.ofReal_pow,Complex.ofReal_re]
  dsimp only [r]
  nlinarith [le_abs_self M,abs_nonneg M,sq_nonneg |M|]

end PowerConvexity
