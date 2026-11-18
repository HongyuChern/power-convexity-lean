import PowerConvexity.Algebra.NormalizeTakagiVector

/-!
# An actual Autonne–Takagi congruence in complex dimension two

This constructs a pointwise unitary matrix with ordered nonnegative diagonal.
No continuity of the chosen frame is asserted or used.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace PowerConvexity

theorem unitary_product_two {P Q : Matrix (Fin 2) (Fin 2) ℂ}
    (hP : P * P.conjTranspose = 1) (hQ : Q * Q.conjTranspose = 1) :
    (P*Q) * (P*Q).conjTranspose = 1 := by
  rw [Matrix.conjTranspose_mul]
  calc
    P * Q * (Q.conjTranspose * P.conjTranspose) =
        P * (Q * Q.conjTranspose) * P.conjTranspose := by noncomm_ring
    _ = 1 := by rw [hQ, Matrix.mul_one, hP]

theorem phase_diagonal_unitary (a b : ℂ)
    (ha : Complex.normSq a = 1) (hb : Complex.normSq b = 1) :
    (Matrix.diagonal ![a,b]) * (Matrix.diagonal ![a,b]).conjTranspose = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      Complex.star_def, Complex.mul_conj, ha, hb]

theorem diagonal_phase_congruence (a b d e : ℂ) :
    (Matrix.diagonal ![a,b]) * (Matrix.diagonal ![d,e]) *
      (Matrix.diagonal ![a,b]).transpose = Matrix.diagonal ![a^2*d,b^2*e] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem exists_takagi_two_unordered {B : Matrix (Fin 2) (Fin 2) ℂ}
    (hB : B.transpose = B) :
    ∃ (Q : Matrix (Fin 2) (Fin 2) ℂ) (d : Fin 2 → ℝ),
      Q * Q.conjTranspose = 1 ∧ (∀ i, 0 ≤ d i) ∧
      Q * B * Q.transpose = Matrix.diagonal (fun i => (d i : ℂ)) := by
  by_cases hz : B = 0
  · refine ⟨1, 0, by simp, ?_, ?_⟩
    · intro i; simp
    · simp [hz]
  obtain ⟨u,t,hu,he⟩ := exists_unit_antilinear_vector_two hB hz
  let P := unitaryCompletionTwo u
  let d := (P*B*P.transpose) 1 1
  have hP : P * P.conjTranspose = 1 := unitaryCompletionTwo_mul_adjoint u hu
  have hdiag : P*B*P.transpose = Matrix.diagonal ![(t:ℂ), d] :=
    unitaryCompletionTwo_congruence hB u t hu he
  obtain ⟨a,ha,hat⟩ := exists_unit_phase_square (t:ℂ)
  obtain ⟨b,hb,hbd⟩ := exists_unit_phase_square d
  let D : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![a,b]
  refine ⟨D*P, ![‖(t:ℂ)‖, ‖d‖],
    unitary_product_two (phase_diagonal_unitary a b ha hb) hP, ?_, ?_⟩
  · intro i; fin_cases i <;> simp
  · rw [Matrix.transpose_mul]
    calc
      D*P*B*(P.transpose*D.transpose) = D*(P*B*P.transpose)*D.transpose := by noncomm_ring
      _ = Matrix.diagonal ![a^2*(t:ℂ), b^2*d] := by
        rw [hdiag]; exact diagonal_phase_congruence a b (t:ℂ) d
      _ = _ := by
        rw [hat,hbd]
        ext i j
        fin_cases i <;> fin_cases j <;> simp

noncomputable def swapMatrixTwo : Matrix (Fin 2) (Fin 2) ℂ := !![0,1;1,0]

theorem swapMatrixTwo_unitary : swapMatrixTwo * swapMatrixTwo.conjTranspose = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [swapMatrixTwo, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]

theorem swapMatrixTwo_diagonal (d : Fin 2 → ℂ) :
    swapMatrixTwo * Matrix.diagonal d * swapMatrixTwo.transpose =
      Matrix.diagonal ![d 1,d 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swapMatrixTwo, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem exists_takagi_two {B : Matrix (Fin 2) (Fin 2) ℂ}
    (hB : B.transpose = B) :
    ∃ (Q : Matrix (Fin 2) (Fin 2) ℂ) (d : Fin 2 → ℝ),
      IsUnit Q.det ∧ Q * Q.conjTranspose = 1 ∧
      0 ≤ d 1 ∧ d 1 ≤ d 0 ∧
      Q * B * Q.transpose = Matrix.diagonal (fun i => (d i : ℂ)) := by
  obtain ⟨P,d,hP,hd,hdiag⟩ := exists_takagi_two_unordered hB
  by_cases horder : d 1 ≤ d 0
  · exact ⟨P,d,Matrix.isUnit_det_of_right_inverse hP,hP,hd 1,horder,hdiag⟩
  · let Q := swapMatrixTwo * P
    have hQ : Q * Q.conjTranspose = 1 := unitary_product_two swapMatrixTwo_unitary hP
    refine ⟨Q, ![d 1,d 0], Matrix.isUnit_det_of_right_inverse hQ,hQ,hd 0,
      (le_of_not_ge horder), ?_⟩
    change (swapMatrixTwo*P)*B*(swapMatrixTwo*P).transpose = _
    rw [Matrix.transpose_mul]
    calc
      _ = swapMatrixTwo*(P*B*P.transpose)*swapMatrixTwo.transpose := by noncomm_ring
      _ = Matrix.diagonal ![(d 1:ℂ),(d 0:ℂ)] := by rw [hdiag,swapMatrixTwo_diagonal]
      _ = _ := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp

end PowerConvexity
