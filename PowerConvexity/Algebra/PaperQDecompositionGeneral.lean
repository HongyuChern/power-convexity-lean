import PowerConvexity.Algebra.WeightedSquares

/-! # Literal finite-dimensional Q61--Q66 bookkeeping

Frozen TeX 827--890. The sign of Q65 at 865--866 is corrected: the cross
term between tau and D in -q(W + tau e - b D) / (1-b^2) is positive.
No positivity or dimension restriction is used in these identities.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped BigOperators
namespace PowerConvexity
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def weightedPair (G : Matrix ι ι ℂ) (v w : ι → ℂ) : ℂ :=
  ∑ p, ∑ q, G q p * v p * star (w q)

theorem weightedSquare_three_term (G : Matrix ι ι ℂ) (W D e : ι → ℂ)
    (τ : ℂ) (b : ℝ) :
    weightedSquare G (fun p => W p + τ * e p - (b : ℂ) * D p) =
      weightedSquare G W + (Complex.normSq τ : ℂ) * weightedSquare G e +
      (b : ℂ)^2 * weightedSquare G D +
      (star τ * weightedPair G W e + τ * weightedPair G e W) -
      (b : ℂ) * (weightedPair G W D + weightedPair G D W) -
      (b : ℂ) * (τ * weightedPair G e D + star τ * weightedPair G D e) := by
  simp only [weightedSquare, weightedPair, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib, star_sub, star_add, star_mul,
    Complex.star_def, Complex.conj_ofReal, Complex.normSq_eq_conj_mul_self]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  ring

theorem weightedSquare_identity (W : ι → ℂ) :
    weightedSquare (1 : Matrix ι ι ℂ) W = ∑ p, (Complex.normSq (W p) : ℂ) := by
  simp only [weightedSquare, Matrix.one_apply]
  simp [Complex.normSq_eq_conj_mul_self, mul_comm]

theorem paper_Q61_split (G : Matrix ι ι ℂ) (W : ι → ℂ)
    (b : ℝ) (hμ : 1 - (b : ℂ)^2 ≠ 0) :
    weightedSquare (G - 1) W - weightedSquare G W / (1 - (b : ℂ)^2) =
      -(∑ p, (Complex.normSq (W p) : ℂ)) -
      (b : ℂ)^2 * weightedSquare G W / (1 - (b : ℂ)^2) := by
  have hsub : weightedSquare (G - 1) W = weightedSquare G W - weightedSquare 1 W := by
    simp [weightedSquare, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]
  rw [hsub, weightedSquare_identity]
  field_simp
  <;> ring

theorem paper_Q63_simplify (q : ℂ) (b : ℝ) (hμ : 1 - (b : ℂ)^2 ≠ 0) :
    -q - (b : ℂ)^2 * q / (1 - (b : ℂ)^2) = -q / (1 - (b : ℂ)^2) := by
  field_simp
  <;> ring

theorem paper_Q64_Q66_simplify (q : ℂ) (b : ℝ) (hμ : 1 - (b : ℂ)^2 ≠ 0) :
    q - q / (1 - (b : ℂ)^2) = -(b : ℂ)^2 * q / (1 - (b : ℂ)^2) := by
  field_simp
  <;> ring

/-- All six Q6 components, including the corrected positive Q65. -/
theorem paper_Q6_completed_square (G : Matrix ι ι ℂ) (W D e : ι → ℂ)
    (τ : ℂ) (b : ℝ) (hμ : 1 - (b : ℂ)^2 ≠ 0) :
    -(b : ℂ)^2 * weightedSquare G W / (1 - (b : ℂ)^2) +
      (b : ℂ) * (weightedPair G W D + weightedPair G D W) / (1 - (b : ℂ)^2) -
      weightedSquare G D / (1 - (b : ℂ)^2) -
      (b : ℂ)^2 * (star τ * weightedPair G W e + τ * weightedPair G e W) /
        (1 - (b : ℂ)^2) +
      (b : ℂ) * (τ * weightedPair G e D + star τ * weightedPair G D e) /
        (1 - (b : ℂ)^2) -
      (b : ℂ)^2 * (Complex.normSq τ : ℂ) * weightedSquare G e / (1 - (b : ℂ)^2) =
    -weightedSquare G (fun p => (b : ℂ) * W p - D p + (b : ℂ) * τ * e p) /
      (1 - (b : ℂ)^2) := by
  apply mul_right_cancel₀ hμ
  simp only [add_mul, sub_mul, div_mul_cancel₀ _ hμ]
  simp only [weightedSquare, weightedPair, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib, star_sub, star_add, star_mul,
    Complex.star_def, Complex.conj_ofReal, Complex.normSq_eq_conj_mul_self]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  ring

/-- The scalar normalization tau = D = i, b = 1/2 distinguishes the two signs.
The original printed Q65 is -4/3; the actual cross contribution is +4/3. -/
theorem paper_Q65_printed_sign_counterexample :
    ((1 / 2 : ℂ) * (Complex.I * star Complex.I + star Complex.I * Complex.I) /
      (1 - (1 / 2 : ℂ)^2) = 4 / 3) ∧
    (-((1 / 2 : ℂ) * (Complex.I * star Complex.I + star Complex.I * Complex.I) /
      (1 - (1 / 2 : ℂ)^2)) ≠ 4 / 3) := by
  norm_num [Complex.star_def, Complex.conj_I, Complex.I_mul_I]

/-- A downstream square-completion interface using the explicit Q expansion. -/
theorem weightedSquare_completion_from_Q (G : Matrix ι ι ℂ) (X D : ι → ℂ)
    (b : ℝ) (hμ : 1 - (b : ℂ)^2 ≠ 0) :
    weightedSquare G D + weightedSquare G (fun p => X p - (b : ℂ) * D p) /
      (1 - (b : ℂ)^2) =
    weightedSquare G X + weightedSquare G (fun p => (b : ℂ) * X p - D p) /
      (1 - (b : ℂ)^2) := by
  have h1 := weightedSquare_three_term G X D (fun _ => 0) 0 b
  have h2 := paper_Q6_completed_square G X D (fun _ => 0) 0 b hμ
  simp only [mul_zero, zero_mul, add_zero, star_zero, Complex.normSq_zero,
    Complex.ofReal_zero, sub_zero, zero_div] at h1 h2
  rw [h1]
  field_simp [hμ] at h2 ⊢
  linear_combination -h2

end PowerConvexity
