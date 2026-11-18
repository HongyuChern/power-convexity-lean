import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

/-! # The literal three-by-three criterion of frozen Lemma A2 -/
set_option autoImplicit false
open scoped Matrix
namespace PowerConvexity

def arrowMatrixThree (A B C β γ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![A, β, γ; β, B, 0; γ, 0, C]

theorem arrowMatrixThree_quadraticForm (A B C β γ : ℝ)
    (hB : B ≠ 0) (hC : C ≠ 0) (v : Fin 3 → ℝ) :
    v ⬝ᵥ (arrowMatrixThree A B C β γ).mulVec v =
      (A-β^2/B-γ^2/C)*(v 0)^2 +
      B*(v 1+β*v 0/B)^2+C*(v 2+γ*v 0/C)^2 := by
  simp only [arrowMatrixThree, dotProduct, Matrix.mulVec, Fin.sum_univ_succ]
  simp
  field_simp
  ring

/-- Exactly the matrix and positive-denominator hypotheses of frozen `A2`. -/
theorem arrowMatrixThree_posSemidef_iff (A B C β γ : ℝ)
    (hB : 0 < B) (hC : 0 < C) :
    (arrowMatrixThree A B C β γ).PosSemidef ↔ 0 ≤ A-β^2/B-γ^2/C := by
  constructor
  · intro h
    have hv := h.dotProduct_mulVec_nonneg ![1,-β/B,-γ/C]
    simp only [star_trivial] at hv
    rw [arrowMatrixThree_quadraticForm A B C β γ hB.ne' hC.ne'] at hv
    simpa [neg_div] using hv
  · intro h
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [arrowMatrixThree]
    · intro v
      simp only [star_trivial]
      rw [arrowMatrixThree_quadraticForm A B C β γ hB.ne' hC.ne']
      exact add_nonneg (add_nonneg (mul_nonneg h (sq_nonneg _))
        (mul_nonneg hB.le (sq_nonneg _))) (mul_nonneg hC.le (sq_nonneg _))

end PowerConvexity
