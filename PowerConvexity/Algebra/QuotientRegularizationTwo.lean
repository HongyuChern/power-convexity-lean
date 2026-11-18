import PowerConvexity.Algebra.HermitianQuotientCoordinatesTwo

/-! # Matrix regularization M + e A and the actual quotient shift K + e I -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped Matrix
namespace PowerConvexity

theorem matrix_quotient_add_smul (M A : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : IsUnit A.det) (e : ℝ) :
    (M+(e:ℂ) • A)*A⁻¹ = M*A⁻¹+(e:ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [Matrix.add_mul,Matrix.smul_mul,Matrix.mul_nonsing_inv (A := A) hA]

theorem trace_add_real_smul_one_two (K : Matrix (Fin 2) (Fin 2) ℂ) (e : ℝ) :
    (K+(e:ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)).trace = K.trace+2*(e:ℂ) := by
  simp [Matrix.trace,Matrix.diag,Fin.sum_univ_two]
  ring

theorem det_add_real_smul_one_two (K : Matrix (Fin 2) (Fin 2) ℂ) (e : ℝ) :
    (K+(e:ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)).det = K.det+(e:ℂ)*K.trace+(e:ℂ)^2 := by
  simp [Matrix.det_fin_two,Matrix.trace,Matrix.diag,Fin.sum_univ_two]
  ring

theorem matrix_quotient_regularized_ratio (M A : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : IsUnit A.det) (e : ℝ) :
    traceDetRatioTwo ((M+(e:ℂ) • A)*A⁻¹).trace.re ((M+(e:ℂ) • A)*A⁻¹).det.re =
      traceDetRatioTwo ((M*A⁻¹).trace.re+2*e)
        ((M*A⁻¹).det.re+e*(M*A⁻¹).trace.re+e^2) := by
  rw [matrix_quotient_add_smul M A hA e,trace_add_real_smul_one_two,det_add_real_smul_one_two]
  congr 1 <;> simp [Complex.mul_re,pow_two]

end PowerConvexity
