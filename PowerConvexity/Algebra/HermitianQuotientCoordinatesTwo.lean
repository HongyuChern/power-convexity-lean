import PowerConvexity.Algebra.TraceDetRatioTwo
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-! # Exact real coordinates for a two by two Hermitian matrix quotient -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped Matrix BigOperators
namespace PowerConvexity

noncomputable def hermitianMatrixTwo (a b c d : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(a:ℂ), (c:ℂ)+Complex.I*(d:ℂ); (c:ℂ)-Complex.I*(d:ℂ), (b:ℂ)]

theorem hermitianMatrixTwo_eq_of_isHermitian (M : Matrix (Fin 2) (Fin 2) ℂ)
    (hM : M.IsHermitian) :
    M = hermitianMatrixTwo (M 0 0).re (M 1 1).re (M 0 1).re (M 0 1).im := by
  have h00 : (M 0 0).im = 0 := by
    have hh := congrArg Complex.im (hM.apply 0 0)
    change -(M 0 0).im = (M 0 0).im at hh
    linarith
  have h11 : (M 1 1).im = 0 := by
    have hh := congrArg Complex.im (hM.apply 1 1)
    change -(M 1 1).im = (M 1 1).im at hh
    linarith
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j
  · apply Complex.ext <;> simp [hermitianMatrixTwo,h00]
  · apply Complex.ext <;> simp [hermitianMatrixTwo]
  · change M 1 0 = hermitianMatrixTwo (M 0 0).re (M 1 1).re (M 0 1).re (M 0 1).im 1 0
    rw [← hM.apply 1 0]
    apply Complex.ext <;> simp [hermitianMatrixTwo]
  · apply Complex.ext <;> simp [hermitianMatrixTwo,h11]

theorem hermitianMatrixTwo_det (a b c d : ℝ) :
    (hermitianMatrixTwo a b c d).det = ((a*b-c^2-d^2:ℝ):ℂ) := by
  apply Complex.ext <;>
    simp [hermitianMatrixTwo,Matrix.det_fin_two,pow_two,Complex.mul_re,Complex.mul_im] <;> ring

theorem hermitianMatrixTwo_trace_mul_adjugate (a b c d A B C D : ℝ) :
    (hermitianMatrixTwo a b c d*(hermitianMatrixTwo A B C D).adjugate).trace =
      ((a*B+b*A-2*(c*C+d*D):ℝ):ℂ) := by
  apply Complex.ext <;>
    simp [hermitianMatrixTwo,Matrix.adjugate_fin_two,Matrix.trace,Matrix.diag,
      Matrix.mul_apply,Fin.sum_univ_two,Complex.mul_re,Complex.mul_im] <;> ring

theorem hermitianMatrixTwo_quotient_trace (a b c d A B C D : ℝ) :
    (hermitianMatrixTwo a b c d*(hermitianMatrixTwo A B C D)⁻¹).trace =
      (((a*B+b*A-2*(c*C+d*D))/(A*B-C^2-D^2):ℝ):ℂ) := by
  rw [Matrix.inv_def,hermitianMatrixTwo_det,Ring.inverse_eq_inv,Matrix.mul_smul,
    Matrix.trace_smul,hermitianMatrixTwo_trace_mul_adjugate]
  push_cast
  simp only [smul_eq_mul]
  ring

theorem hermitianMatrixTwo_quotient_det (a b c d A B C D : ℝ) :
    (hermitianMatrixTwo a b c d*(hermitianMatrixTwo A B C D)⁻¹).det =
      (((a*b-c^2-d^2)/(A*B-C^2-D^2):ℝ):ℂ) := by
  rw [Matrix.det_mul,Matrix.det_nonsing_inv,Ring.inverse_eq_inv,
    hermitianMatrixTwo_det,hermitianMatrixTwo_det]
  push_cast
  rfl

theorem hermitianMatrixTwo_quotient_ratio (a b c d A B C D : ℝ)
    (hDelta : A*B-C^2-D^2 ≠ 0) (hT : a*B+b*A-2*(c*C+d*D) ≠ 0) :
    traceDetRatioTwo
      (hermitianMatrixTwo a b c d*(hermitianMatrixTwo A B C D)⁻¹).trace.re
      (hermitianMatrixTwo a b c d*(hermitianMatrixTwo A B C D)⁻¹).det.re =
      (a*B+b*A-2*(c*C+d*D))/(A*B-C^2-D^2)+
        (a*b-c^2-d^2)/(a*B+b*A-2*(c*C+d*D)) := by
  rw [hermitianMatrixTwo_quotient_trace,hermitianMatrixTwo_quotient_det]
  simp only [Complex.ofReal_re,traceDetRatioTwo]
  rw [div_div_div_cancel_right₀ hDelta]

end PowerConvexity
