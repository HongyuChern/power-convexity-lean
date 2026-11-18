import PowerConvexity.Calculus.UnitaryComplexFrameOrthonormalTwo
import PowerConvexity.Algebra.UnitaryCompletionGeneral
import PowerConvexity.Calculus.SmallContactGaussianBarrierTwo

/-! # Actual unitary frames adapted to every unit vector in the real ambient space -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open Set Matrix
open scoped BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)

theorem actual_standard_real_complex_frame_orthonormal_two :
    Orthonormal ℝ (Sum.elim (realDirections (n := 2)) imagDirections) := by
  rw [orthonormal_iff_ite]
  intro i j
  simp only [blockDirection_eq_single,EuclideanSpace.inner_single_left,conj_trivial,one_mul,
    EuclideanSpace.single_apply]
  simp only [Equiv.apply_eq_iff_eq]

theorem actual_euclidean_unitary_frame_with_normal_two {N : E} (hN : ‖N‖=1) :
    ∃ Q : Matrix (Fin 2) (Fin 2) ℂ, Q*Q.conjTranspose=1 ∧
      Orthonormal ℝ (Sum.elim (complexFrameReal Q realDirections imagDirections)
        (complexFrameImag Q realDirections imagDirections)) ∧
      complexFrameReal Q realDirections imagDirections 1=N := by
  let z : Fin 2 → ℂ := fun i =>
    (inner ℝ N (realDirections i) : ℂ)+Complex.I*(inner ℝ N (imagDirections i) : ℂ)
  have hz : ∑ i, Complex.normSq (z i)=1 := by
    have hh := block_inner_square_sum_two N
    rw [hN,one_pow] at hh
    simp only [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr] at hh
    simp only [z,Complex.normSq_apply,Complex.add_re,Complex.add_im,Complex.ofReal_re,
      Complex.ofReal_im,Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,
      zero_mul,one_mul,sub_zero,zero_add,add_zero]
    rw [Finset.sum_add_distrib]
    simpa only [pow_two] using hh
  have hz1 : (∑ i, z i*star (z i))=1 := by
    have hh := congrArg Complex.ofReal hz
    simpa only [Complex.ofReal_sum,Complex.ofReal_one,Complex.star_def,Complex.mul_conj] using hh
  obtain ⟨Q,hQ,hrow⟩ := exists_unitary_with_row z hz1 1
  refine ⟨Q,hQ,orthonormal_complexFrame_of_unitary_two realDirections imagDirections
    actual_standard_real_complex_frame_orthonormal_two Q hQ,?_⟩
  ext i
  fin_cases i <;>
    simp [complexFrameReal,hrow,z,realDirections,imagDirections,Fin.sum_univ_two,
      EuclideanSpace.inner_single_right,EuclideanSpace.single_apply,finSumFinEquiv]

end PowerConvexity
