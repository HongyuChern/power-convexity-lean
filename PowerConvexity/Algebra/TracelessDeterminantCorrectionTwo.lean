import PowerConvexity.Algebra.HermitianQuotientCoordinatesTwo
import PowerConvexity.Algebra.DeterminantOrderTwo

/-! # Exact positive-branch determinant correction of a traceless Hermitian perturbation.
The scalar correction is explicit. Its size is quadratic in the perturbation
through its determinant. Application to the actual approximating polynomial
must still prove its smallness and positive-branch conditions.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder
namespace PowerConvexity
local notation "W" => Matrix (Fin 2) (Fin 2) ℂ

theorem traceless_hermitian_det_nonpositive_two {A : W}
    (hA : A.IsHermitian) (ht : A.trace = 0) :
    A.det.re ≤ 0 ∧ (A.det.re : ℂ) = A.det := by
  have htr : (A 0 0).re+(A 1 1).re = 0 := by
    have hh := congrArg Complex.re ht
    simpa only [Matrix.trace,Matrix.diag_apply,Fin.sum_univ_two,Complex.add_re,Complex.zero_re] using hh
  have hd : A.det = (((A 0 0).re*(A 1 1).re-(A 0 1).re^2-(A 0 1).im^2 : ℝ) : ℂ) := by
    conv_lhs => rw [hermitianMatrixTwo_eq_of_isHermitian A hA]
    exact hermitianMatrixTwo_det _ _ _ _
  constructor
  · rw [hd,Complex.ofReal_re]
    have h11 : (A 1 1).re = -(A 0 0).re := by linarith only [htr]
    rw [h11]
    nlinarith only [sq_nonneg (A 0 0).re,sq_nonneg (A 0 1).re,sq_nonneg (A 0 1).im]
  · rw [hd,Complex.ofReal_re]

def tracelessDeterminantCorrectionTwo (A : W) : ℝ := Real.sqrt (1-A.det.re)-1

theorem tracelessDeterminantCorrectionTwo_bounds {A : W}
    (hA : A.IsHermitian) (ht : A.trace = 0) :
    0 ≤ tracelessDeterminantCorrectionTwo A ∧
      tracelessDeterminantCorrectionTwo A ≤ -A.det.re ∧
      (1+tracelessDeterminantCorrectionTwo A)^2+A.det.re = 1 := by
  have hd := (traceless_hermitian_det_nonpositive_two hA ht).1
  have harg : 0 ≤ 1-A.det.re := by linarith
  have hs := Real.sqrt_nonneg (1-A.det.re)
  have hs2 := Real.sq_sqrt harg
  have hs1 : 1 ≤ Real.sqrt (1-A.det.re) := by nlinarith
  dsimp only [tracelessDeterminantCorrectionTwo]
  refine ⟨by linarith,?_,by nlinarith⟩
  have hmul := mul_nonneg (sub_nonneg.mpr hs1) hs
  nlinarith

theorem tracelessDeterminantCorrectionTwo_det_one {A : W}
    (hA : A.IsHermitian) (ht : A.trace = 0) :
    ((1+A)+(tracelessDeterminantCorrectionTwo A : ℂ) • (1 : W)).det = 1 := by
  have hdreal := (traceless_hermitian_det_nonpositive_two hA ht).2
  have hid := (tracelessDeterminantCorrectionTwo_bounds hA ht).2.2
  have he : (1+A)+(tracelessDeterminantCorrectionTwo A : ℂ) • (1 : W) =
      A+((1+tracelessDeterminantCorrectionTwo A : ℝ) : ℂ) • (1 : W) := by
    simp only [Complex.ofReal_add,Complex.ofReal_one,add_smul,one_smul]
    abel
  rw [he,det_add_scalar_one_two,ht,mul_zero,add_zero,← hdreal,← Complex.ofReal_pow,← Complex.ofReal_add]
  norm_cast
  linarith only [hid]

theorem tracelessDeterminantCorrectionTwo_posDef {A : W}
    (hA : A.IsHermitian) (ht : A.trace = 0) (hp : (1+A).PosDef) :
    ((1+A)+(tracelessDeterminantCorrectionTwo A : ℂ) • (1 : W)).PosDef := by
  have hδ : (0 : ℂ) ≤ (tracelessDeterminantCorrectionTwo A : ℂ) :=
    Complex.nonneg_iff.mpr ⟨by simpa only [Complex.ofReal_re] using
      (tracelessDeterminantCorrectionTwo_bounds hA ht).1,by simp⟩
  exact hp.add_posSemidef ((Matrix.PosSemidef.one : (1 : W).PosSemidef).smul hδ)

end PowerConvexity
