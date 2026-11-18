import PowerConvexity.Algebra.EigenvaluesTwo
import PowerConvexity.Algebra.TraceDetRatioTwo

/-! # Trace-determinant bounds for the actual Hermitian-similar Schur quotient -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ComplexOrder
namespace PowerConvexity

theorem schur_quotient_trace_det_bounds_two {A B : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : A.PosDef) (hB : B.transpose = B) (hM : (matrixSchur A B).PosSemidef) :
    let K := matrixSchur A B*A⁻¹
    0 ≤ K.trace.re ∧ 0 ≤ K.det.re ∧ K.det.re ≤ K.trace.re^2/4 := by
  let K := matrixSchur A B*A⁻¹
  have hpair := schur_quotient_real_pair hA hB
  have hlow := (schur_posSemidef_iff_lower_nonneg hA hB).mp hM
  rw [lowerEigenvalueTwo_of_real_pair _ _ _ hpair,le_min_iff] at hlow
  obtain ⟨ht,hd⟩ := trace_det_of_charpoly_real_pair _ _ _ hpair
  change 0 ≤ K.trace.re ∧ 0 ≤ K.det.re ∧ K.det.re ≤ K.trace.re^2/4
  dsimp only [K]
  rw [ht,hd]
  simp only [Complex.ofReal_re]
  refine ⟨add_nonneg hlow.1 hlow.2,mul_nonneg hlow.1 hlow.2,?_⟩
  nlinarith [sq_nonneg ((schurHermitianRepresentative_isHermitian hA.isHermitian hB).eigenvalues 0-
    (schurHermitianRepresentative_isHermitian hA.isHermitian hB).eigenvalues 1)]

theorem trace_pos_of_lowerEigenvalueTwo_pos {K : Matrix (Fin 2) (Fin 2) ℂ}
    (h : 0 < lowerEigenvalueTwo K) : 0 < K.trace.re := by
  unfold lowerEigenvalueTwo at h
  linarith [Real.sqrt_nonneg (eigenDiscriminantTwo K)]

theorem eigenDiscriminantTwo_pos_of_lower_zero_trace_pos {K : Matrix (Fin 2) (Fin 2) ℂ}
    (hlow : lowerEigenvalueTwo K = 0) (ht : 0 < K.trace.re) :
    0 < eigenDiscriminantTwo K := by
  apply Real.sqrt_pos.mp
  unfold lowerEigenvalueTwo at hlow
  linarith

theorem traceDetRatioTwo_pos_iff_trace_pos {t d : ℝ}
    (ht : 0 ≤ t) (hd : 0 ≤ d) (hdt : d ≤ t^2/4) :
    0 < traceDetRatioTwo t d ↔ 0 < t := by
  have hb := traceDetRatioTwo_bounds ht hd hdt
  constructor <;> intro h <;> linarith

end PowerConvexity
