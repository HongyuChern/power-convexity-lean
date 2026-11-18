import PowerConvexity.Algebra.MatrixEntryBoundsTwo

/-! # Quantitative bounds for the four normalized residual evaluations -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace PowerConvexity
open CHS.SchurContractionCore

theorem residualEvaluation_difference_corrections_two
    (G R T : Matrix (Fin 2) (Fin 2) ℂ)
    (X Y P P' Q Q' : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ)
    (S S' : Fin 2 → Fin 2 → Matrix (Fin 2) (Fin 2) ℂ) :
    residualEvaluation G R T X Y P Q S-residualEvaluation G R T X Y P' Q' S' =
      contract G (fun p q => (S p q-S' p q)-(P q-P' q)*T*Y p-
        X q*T*(Q p-Q' p)-(P q-P' q)*T*Q p-P' q*T*(Q p-Q' p)) := by
  unfold residualEvaluation
  rw [← contract_sub]
  congr 1
  funext p q
  noncomm_ring

theorem residualEvaluation_entry_bound_two {B : ℝ} (hB : 1 ≤ B)
    (G : Matrix (Fin 2) (Fin 2) ℂ)
    (X Y P Q : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ)
    (S : Fin 2 → Fin 2 → Matrix (Fin 2) (Fin 2) ℂ)
    (hG : matrixEntryBoundTwo G B)
    (hX : ∀ q, matrixEntryBoundTwo (X q) B) (hY : ∀ p, matrixEntryBoundTwo (Y p) B)
    (hP : ∀ q, matrixEntryBoundTwo (P q) (2*B^2))
    (hQ : ∀ p, matrixEntryBoundTwo (Q p) (2*B^2))
    (hS : ∀ p q, matrixEntryBoundTwo (S p q) (8*B^4)) :
    matrixEntryBoundTwo (residualEvaluation G (G.map star) 1 X Y P Q S) (128*B^5) := by
  have hB0 : 0 ≤ B := by linarith
  have hB2 : 0 ≤ 2*B^2 := by positivity
  have hpow : B^3 ≤ B^4 := by
    have hp := mul_le_mul_of_nonneg_right hB (pow_nonneg hB0 3)
    nlinarith
  have hR : matrixEntryBoundTwo (G.map star-1) (2*B) :=
    matrixEntryBoundTwo_mono (matrixEntryBoundTwo_sub (matrixEntryBoundTwo_map_star hG) matrixEntryBoundTwo_one) (by linarith)
  have hF (p q : Fin 2) : matrixEntryBoundTwo
      (X q*(G.map star-1)*Y p+S p q-P q*Y p-X q*Q p-P q*Q p) (32*B^4) := by
    have hXY := matrixEntryBoundTwo_mul (by positivity : 0 ≤ 2*B*(2*B))
      (matrixEntryBoundTwo_mul hB0 (hX q) hR) (hY p)
    have hPY := matrixEntryBoundTwo_mul hB2 (hP q) (hY p)
    have hXQ := matrixEntryBoundTwo_mul hB0 (hX q) (hQ p)
    have hPQ := matrixEntryBoundTwo_mul hB2 (hP q) (hQ p)
    exact matrixEntryBoundTwo_mono (matrixEntryBoundTwo_sub
      (matrixEntryBoundTwo_sub (matrixEntryBoundTwo_sub (matrixEntryBoundTwo_add hXY (hS p q)) hPY) hXQ) hPQ)
      (by nlinarith)
  unfold residualEvaluation
  simp only [Matrix.mul_one]
  convert matrixEntryBoundTwo_contract hB0 hG hF using 1 <;> ring

theorem residualEvaluation_difference_entry_bound_two {B δ : ℝ} (hB : 1 ≤ B) (hδ : 0 ≤ δ)
    (G R : Matrix (Fin 2) (Fin 2) ℂ)
    (X Y P P' Q Q' : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ)
    (S S' : Fin 2 → Fin 2 → Matrix (Fin 2) (Fin 2) ℂ)
    (hG : matrixEntryBoundTwo G B)
    (hX : ∀ q, matrixEntryBoundTwo (X q) B) (hY : ∀ p, matrixEntryBoundTwo (Y p) B)
    (hP' : ∀ q, matrixEntryBoundTwo (P' q) (2*B^2))
    (hQ : ∀ p, matrixEntryBoundTwo (Q p) (2*B^2))
    (hDP : ∀ q, matrixEntryBoundTwo (P q-P' q) (B^2*δ))
    (hDQ : ∀ p, matrixEntryBoundTwo (Q p-Q' p) (B^2*δ))
    (hDS : ∀ p q, matrixEntryBoundTwo (S p q-S' p q) (4*B^4*δ)) :
    matrixEntryBoundTwo
      (residualEvaluation G R 1 X Y P Q S-residualEvaluation G R 1 X Y P' Q' S') (64*B^5*δ) := by
  have hB0 : 0 ≤ B := by linarith
  have hBD : 0 ≤ B^2*δ := by positivity
  have hB2 : 0 ≤ 2*B^2 := by positivity
  have hpow : B^3*δ ≤ B^4*δ := by
    have hp := mul_le_mul_of_nonneg_right hB (pow_nonneg hB0 3)
    have hp' := mul_le_mul_of_nonneg_right hp hδ
    nlinarith
  have hF (p q : Fin 2) : matrixEntryBoundTwo
      ((S p q-S' p q)-(P q-P' q)*Y p-X q*(Q p-Q' p)-
        (P q-P' q)*Q p-P' q*(Q p-Q' p)) (16*B^4*δ) := by
    have hPY := matrixEntryBoundTwo_mul hBD (hDP q) (hY p)
    have hXQ := matrixEntryBoundTwo_mul hB0 (hX q) (hDQ p)
    have hPQ := matrixEntryBoundTwo_mul hBD (hDP q) (hQ p)
    have hP'Q := matrixEntryBoundTwo_mul hB2 (hP' q) (hDQ p)
    exact matrixEntryBoundTwo_mono (matrixEntryBoundTwo_sub (matrixEntryBoundTwo_sub
      (matrixEntryBoundTwo_sub (matrixEntryBoundTwo_sub (hDS p q) hPY) hXQ) hPQ) hP'Q)
      (by nlinarith)
  rw [residualEvaluation_difference_corrections_two]
  simp only [Matrix.mul_one]
  convert matrixEntryBoundTwo_contract hB0 hG hF using 1 <;> ring

end PowerConvexity
