import CHS.CoreImports

/-!
# The dimension-two sign calculation in §3.2

This module proves the finite-dimensional algebra only.  The differential
identification of the paper's `W`, its weighted trace constraint, and the local
eigenvalue differential inequality are separate obligations.
-/

set_option autoImplicit false
open scoped BigOperators ComplexOrder

namespace PowerConvexity

/-- The strict determinant gap following TeX `9.3`. -/
theorem rankOne_weight_gap (w₁ v₁ w₂ v₂ : ℝ) :
    (1 + w₁ ^ 2 + v₁ ^ 2) * (1 + w₂ ^ 2 + v₂ ^ 2) -
        (w₁ * w₂ + v₁ * v₂) ^ 2 - (v₁ * w₂ - w₁ * v₂) ^ 2 =
      1 + w₁ ^ 2 + v₁ ^ 2 + w₂ ^ 2 + v₂ ^ 2 := by ring

/-- TeX `9.2`, under the explicit weighted trace constraint in §3.2. -/
theorem dimensionTwo_scalar_sign (a b c d w₁ v₁ w₂ v₂ : ℝ)
    (htrace : a * (1 + w₁ ^ 2 + v₁ ^ 2) + c * (1 + w₂ ^ 2 + v₂ ^ 2) +
      2 * b * (w₁ * w₂ + v₁ * v₂) - 2 * d * (v₁ * w₂ - w₁ * v₂) = 0) :
    a * c ≤ b ^ 2 + d ^ 2 := by
  let P := 1 + w₁ ^ 2 + v₁ ^ 2
  let X := w₁ * w₂ + v₁ * v₂
  let Y := v₁ * w₂ - w₁ * v₂
  let G := 1 + w₁ ^ 2 + v₁ ^ 2 + w₂ ^ 2 + v₂ ^ 2
  have hP : 0 < P := by dsimp [P]; positivity
  have hG : 0 < G := by dsimp [G]; positivity
  have hid : P ^ 2 * (b ^ 2 + d ^ 2 - a * c) =
      (P * b + c * X) ^ 2 + (P * d - c * Y) ^ 2 + c ^ 2 * G := by
    dsimp [P, X, Y, G]
    linear_combination -(c * (1 + w₁ ^ 2 + v₁ ^ 2)) * htrace
  have hnonneg : 0 ≤ P ^ 2 * (b ^ 2 + d ^ 2 - a * c) := by
    rw [hid]
    positivity
  by_contra h
  have hneg : b ^ 2 + d ^ 2 - a * c < 0 := by linarith
  have hbad := mul_neg_of_pos_of_neg (sq_pos_of_pos hP) hneg
  linarith

/-- A general two-by-two skew-Hermitian matrix in the paper's real parameters. -/
noncomputable def skewMatrixTwo (a b c d : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.I * a, Complex.I * b + d;
     Complex.I * b - d, Complex.I * c]

/-- A positive rank-one perturbation of the identity. -/
noncomputable def rankOneWeightTwo (r : Fin 2 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  1 + Matrix.vecMulVec r (star r)

theorem skewMatrixTwo_conjTranspose (a b c d : ℝ) :
    (skewMatrixTwo a b c d).conjTranspose = -skewMatrixTwo a b c d := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [skewMatrixTwo, Matrix.conjTranspose_apply] <;> ring

/-- The contracted row/column convention is `H q p * W p q`. -/
theorem rankOneWeightTwo_trace_im (a b c d : ℝ) (r : Fin 2 → ℂ) :
    (∑ p, ∑ q, rankOneWeightTwo r q p * skewMatrixTwo a b c d p q).im =
      a * (1 + (r 0).re ^ 2 + (r 0).im ^ 2) +
      c * (1 + (r 1).re ^ 2 + (r 1).im ^ 2) +
      2 * b * ((r 0).re * (r 1).re + (r 0).im * (r 1).im) -
      2 * d * ((r 0).im * (r 1).re - (r 0).re * (r 1).im) := by
  simp [rankOneWeightTwo, skewMatrixTwo, Fin.sum_univ_two,
    Matrix.vecMulVec, Matrix.one_apply, Complex.mul_re, Complex.mul_im]
  ring

/-- TeX `8.1` for the displayed skew-Hermitian parameterization, using `8.2`. -/
theorem dimensionTwo_parameterized_sign (a b c d : ℝ) (r : Fin 2 → ℂ)
    (htrace : (∑ p, ∑ q,
      rankOneWeightTwo r q p * skewMatrixTwo a b c d p q) = 0) :
    Complex.normSq (Matrix.trace (skewMatrixTwo a b c d)) ≤
      ∑ p, ∑ q, Complex.normSq (skewMatrixTwo a b c d p q) := by
  have ht := congrArg Complex.im htrace
  rw [rankOneWeightTwo_trace_im] at ht
  have h := dimensionTwo_scalar_sign a b c d
    (r 0).re (r 0).im (r 1).re (r 1).im ht
  simp [Matrix.trace, skewMatrixTwo, Fin.sum_univ_two, Complex.normSq_apply]
  nlinarith

theorem skewMatrixTwo_representation (W : Matrix (Fin 2) (Fin 2) ℂ)
    (hW : W.conjTranspose = -W) :
    W = skewMatrixTwo (W 0 0).im (W 0 1).im (W 1 1).im (W 0 1).re := by
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => (M 0 0).re) hW
  have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => (M 1 1).re) hW
  have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 0) hW
  have hr := congrArg Complex.re h10
  have hi := congrArg Complex.im h10
  simp only [Matrix.conjTranspose_apply, Matrix.neg_apply, Complex.star_def,
    Complex.conj_re, Complex.neg_re] at h00 h11 hr
  simp only [Matrix.conjTranspose_apply, Matrix.neg_apply, Complex.star_def,
    Complex.conj_im, Complex.neg_im] at hi
  have hr00 : (W 0 0).re = 0 := by linarith
  have hr11 : (W 1 1).re = 0 := by linarith
  have hr10 : (W 1 0).re = -(W 0 1).re := by linarith
  have hi10 : (W 1 0).im = (W 0 1).im := by linarith
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [skewMatrixTwo, Complex.ext_iff, hr00, hr11, hr10, hi10]

theorem rankOneWeightTwo_posDef (r : Fin 2 → ℂ) : (rankOneWeightTwo r).PosDef := by
  exact Matrix.PosDef.one.add_posSemidef (Matrix.posSemidef_vecMulVec_self_star r)

/-- TeX `8.1` for every skew-Hermitian two-by-two matrix under `8.2`.
The contraction uses the inverse matrix's row-column order, not its transpose. -/
theorem dimensionTwo_skew_sign (W : Matrix (Fin 2) (Fin 2) ℂ)
    (hW : W.conjTranspose = -W) (r : Fin 2 → ℂ)
    (htrace : (∑ p, ∑ q, rankOneWeightTwo r q p * W p q) = 0) :
    Complex.normSq (Matrix.trace W) ≤ ∑ p, ∑ q, Complex.normSq (W p q) := by
  have hrepr := skewMatrixTwo_representation W hW
  rw [hrepr] at htrace ⊢
  exact dimensionTwo_parameterized_sign _ _ _ _ r htrace

end PowerConvexity
