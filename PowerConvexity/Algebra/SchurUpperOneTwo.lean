import PowerConvexity.Algebra.TakagiSchurSpectrumTwo

/-! # The upper bound one and its equality case for the lowest Schur root -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ComplexOrder
namespace PowerConvexity

theorem schur_lower_le_one_two {A B : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : A.PosDef) (hB : B.transpose = B) :
    lowerEigenvalueTwo (matrixSchur A B*A⁻¹) ≤ 1 := by
  obtain ⟨Q,d,hQ,hQA,hd1,hd,hQB⟩ := exists_simultaneous_takagi_two hA hB
  rw [(schur_quotient_takagi_ordered_roots A B Q d hQ hQA hQB hd1 hd).1]
  exact sub_le_self _ (sq_nonneg _)

theorem schur_lower_eq_one_iff_two {A B : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : A.PosDef) (hB : B.transpose = B) :
    lowerEigenvalueTwo (matrixSchur A B*A⁻¹) = 1 ↔ B = 0 := by
  obtain ⟨Q,d,hQ,hQA,hd1,hd,hQB⟩ := exists_simultaneous_takagi_two hA hB
  have he := (schur_quotient_takagi_ordered_roots A B Q d hQ hQA hQB hd1 hd).1
  constructor
  · intro hs
    have hd0 : d 0 = 0 := by rw [hs] at he; nlinarith [sq_nonneg (d 0)]
    have hd1z : d 1 = 0 := by linarith
    have hz : Matrix.diagonal (fun i => (d i:ℂ)) = 0 := by
      have hf : (fun i => (d i:ℂ)) = 0 := by funext i; fin_cases i <;> simp [hd0,hd1z]
      rw [hf]
      exact Matrix.diagonal_zero
    rw [hz] at hQB
    have hQt : IsUnit Q.transpose.det := by simpa only [Matrix.det_transpose] using hQ
    calc
      B = (Q⁻¹*Q)*B*(Q.transpose*Q.transpose⁻¹) := by
        rw [Matrix.nonsing_inv_mul Q hQ,Matrix.mul_nonsing_inv Q.transpose hQt,
          Matrix.one_mul,Matrix.mul_one]
      _ = Q⁻¹*(Q*B*Q.transpose)*Q.transpose⁻¹ := by noncomm_ring
      _ = 0 := by rw [hQB,Matrix.mul_zero,Matrix.zero_mul]
  · rintro rfl
    have hz : Matrix.diagonal (fun i => (d i:ℂ)) = 0 := by simpa using hQB.symm
    have hd0 : d 0 = 0 := by
      have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) hz
      simpa using hh
    rw [he,hd0]
    norm_num

end PowerConvexity
