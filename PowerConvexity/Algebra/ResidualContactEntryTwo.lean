import PowerConvexity.Algebra.ReadingTableContactTwo

/-! # From the four matrix residuals to the exact contact Type I expression -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace PowerConvexity
open CHS.Calculus CHS.SchurContractionCore

theorem residual_four_contact_entry_two
    (G W : Matrix (Fin 2) (Fin 2) ℂ) (hW : W.conjTranspose = -W) (τ : ℂ)
    (X₁ X₂ Y₁ Y₂ P₁ P₂ Q₁ Q₂ : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ)
    (S₁ S₂ S₃ S₄ : Fin 2 → Fin 2 → Matrix (Fin 2) (Fin 2) ℂ)
    (hX : ∀ q s, X₁ q 0 s-X₂ q 0 s = W s q)
    (hY : ∀ p t, Y₁ p t 0-Y₂ p t 0 = star (W t p))
    (hP : ∀ q s, P₁ q 0 s-P₂ q 0 s = τ*(1 : Matrix (Fin 2) (Fin 2) ℂ) s q)
    (hQ : ∀ p t, Q₁ p t 0-Q₂ p t 0 = star τ*(1 : Matrix (Fin 2) (Fin 2) ℂ) t p)
    (hS : ∀ p q, S₁ p q 0 0+S₂ p q 0 0-S₃ p q 0 0-S₄ p q 0 0 =
      2*(Complex.normSq τ:ℂ)*(1 : Matrix (Fin 2) (Fin 2) ℂ) p q) :
    (residualEvaluation G (G.map star) 1 X₁ Y₁ P₁ Q₁ S₁+
      residualEvaluation G (G.map star) 1 X₂ Y₂ P₂ Q₂ S₂-
      residualEvaluation G (G.map star) 1 X₁ Y₂ P₁ Q₂ S₃-
      residualEvaluation G (G.map star) 1 X₂ Y₁ P₂ Q₁ S₄) 0 0 =
    typeIQuadraticTwo G W+(Complex.normSq τ:ℂ)*G.trace+
      (τ-star τ)*(∑ p,∑ q,G q p*W p q) := by
  rw [residualEvaluation_four_combination]
  simp only [contract,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  simp only [Matrix.mul_one,Matrix.sub_apply,Matrix.add_apply,Matrix.mul_apply,
    Matrix.map_apply,hX,hY,hP,hQ,hS]
  rw [skewMatrixTwo_representation W hW]
  apply Complex.ext <;>
    simp [typeIQuadraticTwo,skewMatrixTwo,Fin.sum_univ_two,Matrix.trace,Matrix.diag,
      Matrix.one_apply,Complex.star_def,Complex.normSq_apply,Complex.mul_re,Complex.mul_im] <;> ring

theorem residual_four_contact_entry_trace_zero_two
    (G W : Matrix (Fin 2) (Fin 2) ℂ) (hW : W.conjTranspose = -W) (τ : ℂ)
    (X₁ X₂ Y₁ Y₂ P₁ P₂ Q₁ Q₂ : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ)
    (S₁ S₂ S₃ S₄ : Fin 2 → Fin 2 → Matrix (Fin 2) (Fin 2) ℂ)
    (hX : ∀ q s, X₁ q 0 s-X₂ q 0 s = W s q)
    (hY : ∀ p t, Y₁ p t 0-Y₂ p t 0 = star (W t p))
    (hP : ∀ q s, P₁ q 0 s-P₂ q 0 s = τ*(1 : Matrix (Fin 2) (Fin 2) ℂ) s q)
    (hQ : ∀ p t, Q₁ p t 0-Q₂ p t 0 = star τ*(1 : Matrix (Fin 2) (Fin 2) ℂ) t p)
    (hS : ∀ p q, S₁ p q 0 0+S₂ p q 0 0-S₃ p q 0 0-S₄ p q 0 0 =
      2*(Complex.normSq τ:ℂ)*(1 : Matrix (Fin 2) (Fin 2) ℂ) p q)
    (htrace : (∑ p,∑ q,G q p*W p q) = 0) :
    (residualEvaluation G (G.map star) 1 X₁ Y₁ P₁ Q₁ S₁+
      residualEvaluation G (G.map star) 1 X₂ Y₂ P₂ Q₂ S₂-
      residualEvaluation G (G.map star) 1 X₁ Y₂ P₁ Q₂ S₃-
      residualEvaluation G (G.map star) 1 X₂ Y₁ P₂ Q₁ S₄) 0 0 =
    typeIQuadraticTwo G W+(Complex.normSq τ:ℂ)*G.trace := by
  rw [residual_four_contact_entry_two G W hW τ X₁ X₂ Y₁ Y₂ P₁ P₂ Q₁ Q₂
    S₁ S₂ S₃ S₄ hX hY hP hQ hS,htrace,mul_zero,add_zero]

end PowerConvexity
