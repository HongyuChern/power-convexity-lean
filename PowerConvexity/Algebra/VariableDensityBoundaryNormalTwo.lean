import PowerConvexity.Algebra.BoundaryMixedControlTwo

/-! # A bounded positive density controls the normal complex diagonal. -/
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
namespace PowerConvexity

theorem hermitian_det_upper_normal_diagonal_bound_two
    {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.PosDef) {D : ℝ} (hdet : A.det.re ≤ D)
    {delta M : ℝ} (hd : 0 < delta) (ha : delta ≤ (A 0 0).re)
    (hm : Complex.normSq (A 0 1) ≤ M) :
    (A 1 1).re ≤ (D+M)/delta := by
  have h00 := Complex.pos_iff.mp (hA.diag_pos (i := 0))
  have h11 := Complex.pos_iff.mp (hA.diag_pos (i := 1))
  have h10 : A 1 0 = star (A 0 1) := (hA.isHermitian.apply 1 0).symm
  have hid : (A 0 0).re*(A 1 1).re = A.det.re+Complex.normSq (A 0 1) := by
    rw [Matrix.det_fin_two,h10]
    simp only [Complex.sub_re,Complex.mul_re,← h00.2,← h11.2,Complex.star_def,
      Complex.conj_re,Complex.conj_im,zero_mul,sub_zero]
    rw [Complex.normSq_apply]
    ring
  apply (le_div_iff₀ hd).mpr
  have hh := mul_le_mul_of_nonneg_right ha h11.1.le
  nlinarith

end PowerConvexity
