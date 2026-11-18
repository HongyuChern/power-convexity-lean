import PowerConvexity.Algebra.TakagiSchurSpectrumGeneral

/-! # A simple least eigenvalue with multiplicity retained

The diagonal lists every characteristic root, including multiplicity. Thus
strict separation from every other diagonal index is exactly the printed
lambda_1 < lambda_2 when the dimension is at least two.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace PowerConvexity
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def HasSimpleLeastSpectrum (K : Matrix ι ι ℂ) : Prop :=
  ∃ (Q : Matrix ι ι ℂ) (d : ι → ℝ) (i : ι), IsUnit Q.det ∧
    Q*K*Q⁻¹ = Matrix.diagonal (fun j => (d j:ℂ)) ∧
    smallestRealEigenvalue K = d i ∧ ∀ j, j ≠ i → d i < d j

theorem HasSimpleLeastSpectrum.charpoly_factors {K : Matrix ι ι ℂ}
    (hK : HasSimpleLeastSpectrum K) :
    ∃ (d : ι → ℝ) (i : ι), K.charpoly = ∏ j, (Polynomial.X-Polynomial.C (d j:ℂ)) ∧
      smallestRealEigenvalue K = d i ∧ ∀ j, j ≠ i → d i < d j := by
  obtain ⟨Q,d,i,hQ,hdiag,hs,hd⟩ := hK
  refine ⟨d,i,?_,hs,hd⟩
  rw [← charpoly_complex_similarity Q K hQ,hdiag,Matrix.charpoly_diagonal]

theorem hasSimpleLeastSpectrum_of_takagi {A B Q : Matrix ι ι ℂ} {d : ι → ℝ}
    (hQ : IsUnit Q.det) (hA : Q*A*Q.conjTranspose = 1)
    (hB : Q*B*Q.transpose = Matrix.diagonal (fun j => (d j:ℂ)))
    (hd : ∀ j, 0 ≤ d j) (i : ι) (hi : ∀ j, d j ≤ d i)
    (hstrict : ∀ j, j ≠ i → d j < d i) : HasSimpleLeastSpectrum (matrixSchur A B*A⁻¹) := by
  refine ⟨Q,fun j => 1-d j^2,i,hQ,?_,
    schur_quotient_takagi_minimum A B Q d hQ hA hB hd i hi,?_⟩
  · have hs := schur_quotient_complex_similarity Q A B hQ
    rw [hA,hB,matrixSchur_one_real_diagonal,inv_one,Matrix.mul_one] at hs
    exact hs.symm
  · intro j hji
    nlinarith [hstrict j hji,hd j,hd i]

end PowerConvexity
