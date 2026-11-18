import PowerConvexity.Algebra.TakagiRealification
import PowerConvexity.Algebra.UnitPhase

/-! # Explicit unitary completion of a two-dimensional Takagi vector -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace PowerConvexity

noncomputable def unitaryCompletionTwo (u : Fin 2 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![u 0, u 1; -star (u 1), star (u 0)]

theorem unitaryCompletionTwo_mul_adjoint (u : Fin 2 → ℂ)
    (hu : u 0 * star (u 0) + u 1 * star (u 1) = 1) :
    unitaryCompletionTwo u * (unitaryCompletionTwo u).conjTranspose = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unitaryCompletionTwo, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply]
  · exact hu
  · ring
  · ring
  · simpa only [Complex.star_def, mul_comm, add_comm] using hu

theorem symmetric_congruence_transpose {B : Matrix (Fin 2) (Fin 2) ℂ}
    (hB : B.transpose = B) (Q : Matrix (Fin 2) (Fin 2) ℂ) :
    (Q * B * Q.transpose).transpose = Q * B * Q.transpose := by
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hB, Matrix.mul_assoc]

theorem unitaryCompletionTwo_congruence {B : Matrix (Fin 2) (Fin 2) ℂ}
    (hB : B.transpose = B) (u : Fin 2 → ℂ) (t : ℝ)
    (hu : u 0 * star (u 0) + u 1 * star (u 1) = 1)
    (he : B.mulVec u = (t : ℂ) • star u) :
    unitaryCompletionTwo u * B * (unitaryCompletionTwo u).transpose =
      Matrix.diagonal ![(t : ℂ),
        (unitaryCompletionTwo u * B * (unitaryCompletionTwo u).transpose) 1 1] := by
  let P := unitaryCompletionTwo u
  let C := P * B * P.transpose
  have h0 := congrFun he 0
  have h1 := congrFun he 1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Pi.smul_apply, Pi.star_apply, smul_eq_mul] at h0 h1
  have hc00 : C 0 0 = (t : ℂ) := by
    simp only [C, P, unitaryCompletionTwo, Matrix.mul_apply, Matrix.transpose_apply,
      Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    linear_combination u 0 * h0 + u 1 * h1 + (t : ℂ) * hu
  have hc10 : C 1 0 = 0 := by
    simp only [C, P, unitaryCompletionTwo, Matrix.mul_apply, Matrix.transpose_apply,
      Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    linear_combination -star (u 1) * h0 + star (u 0) * h1
  have hct : C.transpose = C := symmetric_congruence_transpose hB P
  have hc01 : C 0 1 = 0 := by
    have h := congrFun (congrFun hct 1) 0
    exact h.trans hc10
  change C = Matrix.diagonal ![(t : ℂ), C 1 1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hc00, hc10, hc01]

end PowerConvexity
