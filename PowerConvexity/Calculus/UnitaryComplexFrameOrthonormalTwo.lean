import PowerConvexity.Calculus.CoordinateCovariance

/-! # A unitary complex frame change preserves the actual real orthonormal frame -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Matrix
open scoped BigOperators
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem orthonormal_complexFrame_of_unitary_two
    (a b : Fin 2 → E) (hab : Orthonormal ℝ (Sum.elim a b))
    (Q : Matrix (Fin 2) (Fin 2) ℂ) (hQ : Q*Q.conjTranspose = 1) :
    Orthonormal ℝ (Sum.elim (complexFrameReal Q a b) (complexFrameImag Q a b)) := by
  have haa (i j : Fin 2) : inner ℝ (a i) (a j) = if i=j then 1 else 0 := by
    simpa using orthonormal_iff_ite.mp hab (Sum.inl i) (Sum.inl j)
  have hbb (i j : Fin 2) : inner ℝ (b i) (b j) = if i=j then 1 else 0 := by
    simpa using orthonormal_iff_ite.mp hab (Sum.inr i) (Sum.inr j)
  have hab0 (i j : Fin 2) : inner ℝ (a i) (b j) = 0 := by
    simpa using orthonormal_iff_ite.mp hab (Sum.inl i) (Sum.inr j)
  have hba0 (i j : Fin 2) : inner ℝ (b i) (a j) = 0 := by
    simpa using orthonormal_iff_ite.mp hab (Sum.inr i) (Sum.inl j)
  have hrr (i j : Fin 2) : inner ℝ (complexFrameReal Q a b i) (complexFrameReal Q a b j) =
      ((Q*Q.conjTranspose) i j).re := by
    simp only [complexFrameReal,Fin.sum_univ_two,inner_add_left,inner_add_right,
      real_inner_smul_left,real_inner_smul_right,haa,hbb,hab0,hba0]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply,Matrix.conjTranspose_apply,Fin.sum_univ_two,
        Complex.add_re,Complex.mul_re,Complex.star_def] <;> ring
  have hii (i j : Fin 2) : inner ℝ (complexFrameImag Q a b i) (complexFrameImag Q a b j) =
      ((Q*Q.conjTranspose) i j).re := by
    simp only [complexFrameImag,Fin.sum_univ_two,inner_add_left,inner_add_right,
      inner_sub_left,inner_sub_right,real_inner_smul_left,real_inner_smul_right,haa,hbb,hab0,hba0]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply,Matrix.conjTranspose_apply,Fin.sum_univ_two,
        Complex.add_re,Complex.mul_re,Complex.star_def] <;> ring
  have hri (i j : Fin 2) : inner ℝ (complexFrameReal Q a b i) (complexFrameImag Q a b j) =
      ((Q*Q.conjTranspose) i j).im := by
    simp only [complexFrameReal,complexFrameImag,Fin.sum_univ_two,inner_add_left,inner_add_right,
      inner_sub_left,inner_sub_right,real_inner_smul_left,real_inner_smul_right,haa,hbb,hab0,hba0]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply,Matrix.conjTranspose_apply,Fin.sum_univ_two,
        Complex.add_im,Complex.mul_im,Complex.star_def] <;> ring
  rw [orthonormal_iff_ite]
  intro i j
  cases i with
  | inl i =>
    cases j with
    | inl j => by_cases h : i=j <;> simpa [hQ,Matrix.one_apply,h] using hrr i j
    | inr j => by_cases h : i=j <;> simpa [hQ,Matrix.one_apply,h] using hri i j
  | inr i =>
    cases j with
    | inl j => by_cases h : j=i <;> simpa [hQ,Matrix.one_apply,h,real_inner_comm] using hri j i
    | inr j => by_cases h : i=j <;> simpa [hQ,Matrix.one_apply,h] using hii i j

end PowerConvexity
