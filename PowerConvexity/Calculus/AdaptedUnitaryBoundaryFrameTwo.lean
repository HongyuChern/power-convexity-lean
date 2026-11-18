import PowerConvexity.Calculus.UnitaryComplexFrameOrthonormalTwo
import PowerConvexity.Calculus.FrameDualQuadratics
import PowerConvexity.Algebra.UnitaryCompletionGeneral

/-! # An actual unitary complex frame adapted to a nonzero real boundary normal -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Matrix
open scoped BigOperators
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]

theorem exists_unitary_complex_frame_with_normal_two
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {N : E} (hN : N ≠ 0) :
    ∃ (Q : Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ), 0 < r ∧ Q*Q.conjTranspose = 1 ∧
      Orthonormal ℝ (Sum.elim (complexFrameReal Q e (fun j => Complex.I • e j))
        (complexFrameImag Q e (fun j => Complex.I • e j))) ∧
      complexFrameReal Q e (fun j => Complex.I • e j) 1 = r⁻¹ • N := by
  classical
  have hz : ∃ j : Fin 2, e.repr N j ≠ 0 := by
    by_contra h
    push_neg at h
    apply hN
    apply e.repr.injective
    ext j
    simpa using h j
  obtain ⟨j,hj⟩ := hz
  let S : ℝ := ∑ i : Fin 2, Complex.normSq (e.repr N i)
  have hS : 0 < S := Finset.sum_pos' (fun i _ => Complex.normSq_nonneg _)
    ⟨j,Finset.mem_univ _,Complex.normSq_pos.mpr hj⟩
  let r : ℝ := Real.sqrt S
  have hr : 0 < r := Real.sqrt_pos.mpr hS
  have hrs : r*r = S := by simpa only [← pow_two] using Real.sq_sqrt hS.le
  let z : Fin 2 → ℂ := fun i => (r : ℂ)⁻¹*e.repr N i
  have hzSq : ∑ i, Complex.normSq (z i) = 1 := by
    simp only [z,map_mul,Complex.normSq_inv,Complex.normSq_ofReal]
    rw [← Finset.mul_sum,hrs]
    exact inv_mul_cancel₀ hS.ne'
  have hzOne : (∑ i, z i*star (z i)) = 1 := by
    have hh := congrArg Complex.ofReal hzSq
    simpa only [Complex.ofReal_sum,Complex.ofReal_one,Complex.star_def,Complex.mul_conj] using hh
  obtain ⟨Q,hQ,hrow⟩ := exists_unitary_with_row z hzOne 1
  refine ⟨Q,r,hr,hQ,orthonormal_complexFrame_of_unitary_two e _ hab Q hQ,?_⟩
  rw [complexFrameReal_complex_basis]
  simp_rw [hrow,z,mul_smul]
  rw [← Finset.smul_sum,e.sum_repr N,← Complex.ofReal_inv]
  simpa only [RCLike.ofReal_eq_complex_ofReal] using
    (RCLike.real_smul_eq_coe_smul (K := ℂ) r⁻¹ N).symm

theorem exists_unitary_defining_tangent_frame_two
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    (D : E →L[ℝ] ℝ) {N : E} (hN : N ≠ 0)
    (hD : ∀ v : E, D v = inner ℝ N v) :
    ∃ (Q : Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ), 0 < r ∧ Q*Q.conjTranspose = 1 ∧
      Orthonormal ℝ (Sum.elim (complexFrameReal Q e (fun j => Complex.I • e j))
        (complexFrameImag Q e (fun j => Complex.I • e j))) ∧
      complexFrameReal Q e (fun j => Complex.I • e j) 1 = r⁻¹ • N ∧
      D (complexFrameReal Q e (fun j => Complex.I • e j) 0) = 0 ∧
      D (complexFrameImag Q e (fun j => Complex.I • e j) 0) = 0 ∧
      D (complexFrameImag Q e (fun j => Complex.I • e j) 1) = 0 := by
  obtain ⟨Q,r,hr,hQ,hframe,hnormal⟩ := exists_unitary_complex_frame_with_normal_two e hab hN
  let a := complexFrameReal Q e (fun j => Complex.I • e j)
  let b := complexFrameImag Q e (fun j => Complex.I • e j)
  have hNr : N = r • a 1 := by rw [show a 1 = r⁻¹ • N from hnormal,smul_smul,mul_inv_cancel₀ hr.ne',one_smul]
  have ht0 : inner ℝ (a 1) (a 0) = 0 := by
    simpa [a] using
      orthonormal_iff_ite.mp hframe (Sum.inl 1) (Sum.inl 0)
  have ht1 : inner ℝ (a 1) (b 0) = 0 := by
    simpa using orthonormal_iff_ite.mp hframe (Sum.inl 1) (Sum.inr 0)
  have ht2 : inner ℝ (a 1) (b 1) = 0 := by
    simpa using orthonormal_iff_ite.mp hframe (Sum.inl 1) (Sum.inr 1)
  refine ⟨Q,r,hr,hQ,hframe,hnormal,?_,?_,?_⟩
  · rw [hD,hNr,real_inner_smul_left,ht0,mul_zero]
  · rw [hD,hNr,real_inner_smul_left,ht1,mul_zero]
  · rw [hD,hNr,real_inner_smul_left,ht2,mul_zero]

end PowerConvexity
