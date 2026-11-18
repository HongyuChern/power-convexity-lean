import PowerConvexity.Algebra.UnitaryCompletionTwo

/-! # Normalizing the antilinear eigenvector without changing its eigenvalue -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace PowerConvexity

theorem exists_unit_antilinear_vector_two {B : Matrix (Fin 2) (Fin 2) ℂ}
    (hB : B.transpose = B) (hB0 : B ≠ 0) :
    ∃ (u : Fin 2 → ℂ) (t : ℝ),
      u 0 * star (u 0) + u 1 * star (u 1) = 1 ∧
      B.mulVec u = (t : ℂ) • star u := by
  obtain ⟨z, t, _, hz, he⟩ := exists_antilinear_eigenvector_of_symmetric hB hB0
  let S : ℝ := Complex.normSq (z 0) + Complex.normSq (z 1)
  have hS : 0 < S := by
    have h0 := Complex.normSq_nonneg (z 0)
    have h1 := Complex.normSq_nonneg (z 1)
    by_contra h
    have hs0 : S = 0 := by dsimp [S] at *; linarith
    have hz0 : z 0 = 0 := Complex.normSq_eq_zero.mp (by dsimp [S] at hs0; linarith)
    have hz1 : z 1 = 0 := Complex.normSq_eq_zero.mp (by dsimp [S] at hs0; linarith)
    apply hz
    funext i
    fin_cases i <;> simp [hz0, hz1]
  let r := Real.sqrt S
  have hr : r ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hS)
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  have hrsq : r^2 = S := Real.sq_sqrt hS.le
  let u : Fin 2 → ℂ := (r : ℂ)⁻¹ • star z
  have huNorm : Complex.normSq (u 0) + Complex.normSq (u 1) = 1 := by
    simp only [u, Pi.smul_apply, Pi.star_apply, smul_eq_mul, map_mul,
      Complex.normSq_inv, Complex.normSq_ofReal, Complex.star_def, Complex.normSq_conj]
    field_simp
    dsimp [S] at hrsq
    nlinarith
  refine ⟨u, t, ?_, ?_⟩
  · have h := congrArg Complex.ofReal huNorm
    simpa only [Complex.ofReal_add, Complex.ofReal_one, Complex.star_def,
      Complex.mul_conj] using h
  · rw [Matrix.mulVec_smul, he]
    funext i
    change (r : ℂ)⁻¹ * ((t : ℂ) * z i) =
      (t : ℂ) * star ((r : ℂ)⁻¹ * star (z i))
    simp only [star_mul, star_inv₀, star_star]
    have hs : star (r : ℂ) = (r : ℂ) := by simp [Complex.star_def]
    rw [hs]
    ring

end PowerConvexity
