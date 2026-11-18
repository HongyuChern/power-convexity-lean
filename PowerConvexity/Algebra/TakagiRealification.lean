import PowerConvexity.Algebra.SchurSpectrum

/-! # Real symmetric realization of a complex symmetric antilinear map -/
set_option autoImplicit false
open scoped BigOperators
namespace PowerConvexity
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def antiLinearRealification (B : Matrix ι ι ℂ) :
    Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
  Matrix.fromBlocks (B.map Complex.re) (B.map Complex.im)
    (B.map Complex.im) (-(B.map Complex.re))

noncomputable def complexVectorOfReal (v : (ι ⊕ ι) → ℝ) : ι → ℂ :=
  fun i => ⟨v (.inl i), v (.inr i)⟩

theorem antiLinearRealification_isHermitian {B : Matrix ι ι ℂ}
    (hB : B.transpose = B) : (antiLinearRealification B).IsHermitian := by
  have hs (i j : ι) : B j i = B i j := congrFun (congrFun hB i) j
  ext (i | i) (j | j) <;>
    simp only [Matrix.conjTranspose_apply, star_trivial, antiLinearRealification,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.map_apply,
      Matrix.neg_apply, hs]

theorem antiLinearRealification_ne_zero {B : Matrix ι ι ℂ} (hB : B ≠ 0) :
    antiLinearRealification B ≠ 0 := by
  intro hz
  apply hB
  ext i j
  apply Complex.ext
  · exact congrArg (fun M : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ => M (.inl i) (.inl j)) hz
  · exact congrArg (fun M : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ => M (.inl i) (.inr j)) hz

theorem complexVectorOfReal_ne_zero {v : (ι ⊕ ι) → ℝ} (hv : v ≠ 0) :
    complexVectorOfReal v ≠ 0 := by
  intro hz
  apply hv
  funext i
  rcases i with i | i
  · exact congrArg Complex.re (congrFun hz i)
  · exact congrArg Complex.im (congrFun hz i)

theorem antiLinearRealification_eigenvector {B : Matrix ι ι ℂ}
    {v : (ι ⊕ ι) → ℝ} {t : ℝ}
    (he : (antiLinearRealification B).mulVec v = t • v) :
    B.mulVec (star (complexVectorOfReal v)) = (t : ℂ) • complexVectorOfReal v := by
  funext i
  have hr := congrFun he (.inl i)
  have hi := congrFun he (.inr i)
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    antiLinearRealification, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.map_apply,
    Matrix.neg_apply, Pi.smul_apply, smul_eq_mul, neg_mul] at hr hi
  apply Complex.ext
  · simpa only [Matrix.mulVec, dotProduct, Complex.re_sum, Pi.star_apply,
      Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      complexVectorOfReal, mul_neg, sub_neg_eq_add,
      Finset.sum_add_distrib, Pi.smul_apply, smul_eq_mul,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using hr
  · simpa only [Matrix.mulVec, dotProduct, Complex.im_sum, Pi.star_apply,
      Complex.star_def, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      complexVectorOfReal, mul_neg,
      Finset.sum_add_distrib, Pi.smul_apply, smul_eq_mul,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, zero_add,
      Finset.sum_neg_distrib, add_comm] using hi

theorem exists_antilinear_eigenvector_of_symmetric {B : Matrix ι ι ℂ}
    (hB : B.transpose = B) (hB0 : B ≠ 0) :
    ∃ (z : ι → ℂ) (t : ℝ), t ≠ 0 ∧ z ≠ 0 ∧ B.mulVec (star z) = (t : ℂ) • z := by
  have hsym := antiLinearRealification_isHermitian hB
  obtain ⟨v, t, ht, hv, he⟩ := hsym.exists_eigenvector_of_ne_zero
    (antiLinearRealification_ne_zero hB0)
  exact ⟨complexVectorOfReal v, t, ht, complexVectorOfReal_ne_zero hv,
    antiLinearRealification_eigenvector he⟩

end PowerConvexity
