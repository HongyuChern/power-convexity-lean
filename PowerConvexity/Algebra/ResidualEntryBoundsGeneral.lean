import PowerConvexity.Algebra.MatrixEntryBoundsGeneral

/-! # Quantitative bounds for the four normalized residual evaluations -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace PowerConvexity
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
open CHS.SchurContractionCore

theorem residualEvaluation_difference_corrections_general
    (G R T : Matrix ι ι ℂ)
    (X Y P P' Q Q' : ι → Matrix ι ι ℂ)
    (S S' : ι → ι → Matrix ι ι ℂ) :
    residualEvaluation G R T X Y P Q S-residualEvaluation G R T X Y P' Q' S' =
      contract G (fun p q => (S p q-S' p q)-(P q-P' q)*T*Y p-
        X q*T*(Q p-Q' p)-(P q-P' q)*T*Q p-P' q*T*(Q p-Q' p)) := by
  unfold residualEvaluation
  rw [← contract_sub]
  congr 1
  funext p q
  noncomm_ring

theorem residualEvaluation_entry_bound_general {B : ℝ} (hB : 1 ≤ B)
    (G : Matrix ι ι ℂ)
    (X Y P Q : ι → Matrix ι ι ℂ)
    (S : ι → ι → Matrix ι ι ℂ)
    (hG : matrixEntryBoundGeneral G B)
    (hX : ∀ q, matrixEntryBoundGeneral (X q) B) (hY : ∀ p, matrixEntryBoundGeneral (Y p) B)
    (hP : ∀ q, matrixEntryBoundGeneral (P q) (2*B^2))
    (hQ : ∀ p, matrixEntryBoundGeneral (Q p) (2*B^2))
    (hS : ∀ p q, matrixEntryBoundGeneral (S p q) (8*B^4)) :
    matrixEntryBoundGeneral (residualEvaluation G (G.map star) 1 X Y P Q S) ((Fintype.card ι : ℝ)^2*(2*(Fintype.card ι : ℝ)^2+8*(Fintype.card ι : ℝ)+8)*B^5) := by
  let n : ℝ := Fintype.card ι
  have hn : 0 ≤ n := by dsimp [n]; positivity
  have hB0 : 0 ≤ B := by linarith
  have hB2 : 0 ≤ 2*B^2 := by positivity
  have hpow : B^3 ≤ B^4 := by
    have hp := mul_le_mul_of_nonneg_right hB (pow_nonneg hB0 3)
    nlinarith
  have hR : matrixEntryBoundGeneral (G.map star-1) (2*B) :=
    matrixEntryBoundGeneral_mono (matrixEntryBoundGeneral_sub (matrixEntryBoundGeneral_map_star hG) matrixEntryBoundGeneral_one) (by linarith)
  have hF (p q : ι) : matrixEntryBoundGeneral
      (X q*(G.map star-1)*Y p+S p q-P q*Y p-X q*Q p-P q*Q p) ((2*n^2+8*n+8)*B^4) := by
    have hXY := matrixEntryBoundGeneral_mul (by positivity : 0 ≤ (Fintype.card ι : ℝ)*B*(2*B))
      (matrixEntryBoundGeneral_mul hB0 (hX q) hR) (hY p)
    have hPY := matrixEntryBoundGeneral_mul hB2 (hP q) (hY p)
    have hXQ := matrixEntryBoundGeneral_mul hB0 (hX q) (hQ p)
    have hPQ := matrixEntryBoundGeneral_mul hB2 (hP q) (hQ p)
    exact matrixEntryBoundGeneral_mono (matrixEntryBoundGeneral_sub
      (matrixEntryBoundGeneral_sub (matrixEntryBoundGeneral_sub (matrixEntryBoundGeneral_add hXY (hS p q)) hPY) hXQ) hPQ)
      (by
        have hp1 := mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ 2*n^2)
        have hp2 := mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ 4*n)
        change n*(n*B*(2*B))*B+8*B^4+n*(2*B^2)*B+n*B*(2*B^2)+n*(2*B^2)*(2*B^2) ≤ _
        nlinarith)
  unfold residualEvaluation
  simp only [Matrix.mul_one]
  convert matrixEntryBoundGeneral_contract hB0 hG hF using 1 <;> dsimp [n] <;> ring

theorem residualEvaluation_difference_entry_bound_general {B δ : ℝ} (hB : 1 ≤ B) (hδ : 0 ≤ δ)
    (G R : Matrix ι ι ℂ)
    (X Y P P' Q Q' : ι → Matrix ι ι ℂ)
    (S S' : ι → ι → Matrix ι ι ℂ)
    (hG : matrixEntryBoundGeneral G B)
    (hX : ∀ q, matrixEntryBoundGeneral (X q) B) (hY : ∀ p, matrixEntryBoundGeneral (Y p) B)
    (hP' : ∀ q, matrixEntryBoundGeneral (P' q) (2*B^2))
    (hQ : ∀ p, matrixEntryBoundGeneral (Q p) (2*B^2))
    (hDP : ∀ q, matrixEntryBoundGeneral (P q-P' q) (B^2*δ))
    (hDQ : ∀ p, matrixEntryBoundGeneral (Q p-Q' p) (B^2*δ))
    (hDS : ∀ p q, matrixEntryBoundGeneral (S p q-S' p q) (4*B^4*δ)) :
    matrixEntryBoundGeneral
      (residualEvaluation G R 1 X Y P Q S-residualEvaluation G R 1 X Y P' Q' S') ((Fintype.card ι : ℝ)^2*(4+6*(Fintype.card ι : ℝ))*B^5*δ) := by
  let n : ℝ := Fintype.card ι
  have hn : 0 ≤ n := by dsimp [n]; positivity
  have hB0 : 0 ≤ B := by linarith
  have hBD : 0 ≤ B^2*δ := by positivity
  have hB2 : 0 ≤ 2*B^2 := by positivity
  have hpow : B^3*δ ≤ B^4*δ := by
    have hp := mul_le_mul_of_nonneg_right hB (pow_nonneg hB0 3)
    have hp' := mul_le_mul_of_nonneg_right hp hδ
    nlinarith
  have hF (p q : ι) : matrixEntryBoundGeneral
      ((S p q-S' p q)-(P q-P' q)*Y p-X q*(Q p-Q' p)-
        (P q-P' q)*Q p-P' q*(Q p-Q' p)) ((4+6*n)*B^4*δ) := by
    have hPY := matrixEntryBoundGeneral_mul hBD (hDP q) (hY p)
    have hXQ := matrixEntryBoundGeneral_mul hB0 (hX q) (hDQ p)
    have hPQ := matrixEntryBoundGeneral_mul hBD (hDP q) (hQ p)
    have hP'Q := matrixEntryBoundGeneral_mul hB2 (hP' q) (hDQ p)
    exact matrixEntryBoundGeneral_mono (matrixEntryBoundGeneral_sub (matrixEntryBoundGeneral_sub
      (matrixEntryBoundGeneral_sub (matrixEntryBoundGeneral_sub (hDS p q) hPY) hXQ) hPQ) hP'Q)
      (by
        have hp := mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ 2*n)
        change 4*B^4*δ+n*(B^2*δ)*B+n*B*(B^2*δ)+n*(B^2*δ)*(2*B^2)+n*(2*B^2)*(B^2*δ) ≤ _
        nlinarith)
  rw [residualEvaluation_difference_corrections_general]
  simp only [Matrix.mul_one]
  convert matrixEntryBoundGeneral_contract hB0 hG hF using 1 <;> dsimp [n] <;> ring

end PowerConvexity
