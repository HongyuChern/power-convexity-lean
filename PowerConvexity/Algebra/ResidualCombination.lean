import PowerConvexity.Calculus.ModifiedResidualEvaluation

/-! # The exact four-row combination underlying ReadingTable -/
set_option autoImplicit false
open scoped BigOperators
namespace PowerConvexity
open CHS.SchurContractionCore
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem residualEvaluation_four_combination
    (W R T : Matrix ι ι ℂ) (X₁ X₂ Y₁ Y₂ P₁ P₂ Q₁ Q₂ : ι → Matrix ι ι ℂ)
    (S₁ S₂ S₃ S₄ : ι → ι → Matrix ι ι ℂ) :
    residualEvaluation W R T X₁ Y₁ P₁ Q₁ S₁ +
      residualEvaluation W R T X₂ Y₂ P₂ Q₂ S₂ -
      residualEvaluation W R T X₁ Y₂ P₁ Q₂ S₃ -
      residualEvaluation W R T X₂ Y₁ P₂ Q₁ S₄ =
    contract W (fun p q =>
      (X₁ q-X₂ q)*(R-T)*(Y₁ p-Y₂ p)+(S₁ p q+S₂ p q-S₃ p q-S₄ p q)-
      (P₁ q-P₂ q)*T*(Y₁ p-Y₂ p)-(X₁ q-X₂ q)*T*(Q₁ p-Q₂ p)-
      (P₁ q-P₂ q)*T*(Q₁ p-Q₂ p)) := by
  unfold residualEvaluation
  rw [← contract_add,← contract_sub,← contract_sub]
  congr 1
  funext p q
  noncomm_ring

end PowerConvexity
