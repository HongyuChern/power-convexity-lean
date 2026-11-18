import PowerConvexity.Algebra.Congruence

/-!
# A Hermitian representative of the Schur quotient

The quotient `M A⁻¹` is generally not Hermitian.  We construct the actual
inverse-square-root normalization, prove its similarity relation, and transfer
its characteristic polynomial to a Hermitian matrix.  This is pointwise
spectral algebra; smooth selection of a lowest eigenvalue is a separate step.
-/

set_option autoImplicit false
open Matrix
open scoped ComplexOrder MatrixOrder

namespace PowerConvexity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def whiteningMatrix (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (CFC.sqrt A)⁻¹

theorem whiteningMatrix_normalizes {A : Matrix ι ι ℂ} (hA : A.PosDef) :
    IsUnit (whiteningMatrix A).det ∧
      whiteningMatrix A * A * (whiteningMatrix A).conjTranspose = 1 := by
  let S := CFC.sqrt A
  have hS : S.PosSemidef := (CFC.sqrt_nonneg A).posSemidef
  have hSq : S * S = A := by
    simpa only [pow_two] using CFC.sq_sqrt A hA.posSemidef.nonneg
  have hAu : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit
  have hSu : IsUnit S.det := by
    rw [← hSq, Matrix.det_mul] at hAu
    exact isUnit_of_mul_isUnit_left hAu
  have hSinv := hS.isHermitian.inv
  change IsUnit S⁻¹.det ∧ S⁻¹ * A * S⁻¹.conjTranspose = 1
  refine ⟨Matrix.isUnit_nonsing_inv_det _ hSu, ?_⟩
  rw [hSinv.eq, ← hSq, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hSu,
    Matrix.one_mul, Matrix.mul_nonsing_inv _ hSu]

theorem exists_complex_normalization {A : Matrix ι ι ℂ} (hA : A.PosDef) :
    ∃ Q : Matrix ι ι ℂ, IsUnit Q.det ∧ Q * A * Q.conjTranspose = 1 :=
  ⟨whiteningMatrix A, whiteningMatrix_normalizes hA⟩

theorem matrixSchur_isHermitian {A B : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (hB : B.transpose = B) :
    (matrixSchur A B).IsHermitian := by
  have hAb : A.map star = A.transpose := by
    ext i j
    exact hA.apply j i
  have hBb : B.map star = B.conjTranspose := by
    have h := congrArg (fun M : Matrix ι ι ℂ => M.map star) hB
    exact h.symm
  unfold matrixSchur
  rw [hAb, hBb]
  exact hA.sub (Matrix.isHermitian_mul_mul_conjTranspose B hA.transpose.inv)

noncomputable def schurHermitianRepresentative (A B : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  whiteningMatrix A * matrixSchur A B * (whiteningMatrix A).conjTranspose

theorem schurHermitianRepresentative_isHermitian {A B : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (hB : B.transpose = B) :
    (schurHermitianRepresentative A B).IsHermitian := by
  exact Matrix.isHermitian_mul_mul_conjTranspose _ (matrixSchur_isHermitian hA hB)

theorem schurHermitianRepresentative_similarity {A B : Matrix ι ι ℂ}
    (hA : A.PosDef) :
    schurHermitianRepresentative A B =
      whiteningMatrix A * (matrixSchur A B * A⁻¹) * (whiteningMatrix A)⁻¹ := by
  obtain ⟨hQ, hnorm⟩ := whiteningMatrix_normalizes hA
  have h := congruence_quotient_similarity (whiteningMatrix A) (matrixSchur A B) A hQ
  rw [hnorm, inv_one, Matrix.mul_one] at h
  exact h

theorem charpoly_complex_similarity (Q K : Matrix ι ι ℂ) (hQ : IsUnit Q.det) :
    (Q * K * Q⁻¹).charpoly = K.charpoly := by
  rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ hQ, Matrix.one_mul]

theorem schur_quotient_charpoly_hermitian {A B : Matrix ι ι ℂ}
    (hA : A.PosDef) :
    (matrixSchur A B * A⁻¹).charpoly = (schurHermitianRepresentative A B).charpoly := by
  rw [schurHermitianRepresentative_similarity hA]
  exact (charpoly_complex_similarity _ _ (whiteningMatrix_normalizes hA).1).symm

/-- The characteristic roots of the quotient are precisely the real
eigenvalues of its Hermitian representative, counted with multiplicity. -/
theorem schur_quotient_charpoly_real_factors {A B : Matrix ι ι ℂ}
    (hA : A.PosDef) (hB : B.transpose = B) :
    (matrixSchur A B * A⁻¹).charpoly =
      ∏ i, (Polynomial.X - Polynomial.C
        ((schurHermitianRepresentative_isHermitian hA.isHermitian hB).eigenvalues i : ℂ)) := by
  rw [schur_quotient_charpoly_hermitian hA]
  exact (schurHermitianRepresentative_isHermitian hA.isHermitian hB).charpoly_eq

end PowerConvexity
