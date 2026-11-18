import PowerConvexity.Algebra.ResidualCombination
import PowerConvexity.Algebra.TypeICompletionGeneral

/-! # From the four matrix residuals to the exact contact Type I expression -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace PowerConvexity
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
open CHS.Calculus CHS.SchurContractionCore

theorem residual_four_contact_entry
    (k : ι) (G W : Matrix ι ι ℂ) (hW : W.conjTranspose = -W) (τ : ℂ)
    (X₁ X₂ Y₁ Y₂ P₁ P₂ Q₁ Q₂ : ι → Matrix ι ι ℂ)
    (S₁ S₂ S₃ S₄ : ι → ι → Matrix ι ι ℂ)
    (hX : ∀ q s, X₁ q k s-X₂ q k s = W s q)
    (hY : ∀ p t, Y₁ p t k-Y₂ p t k = star (W t p))
    (hP : ∀ q s, P₁ q k s-P₂ q k s = τ*(1 : Matrix ι ι ℂ) s q)
    (hQ : ∀ p t, Q₁ p t k-Q₂ p t k = star τ*(1 : Matrix ι ι ℂ) t p)
    (hS : ∀ p q, S₁ p q k k+S₂ p q k k-S₃ p q k k-S₄ p q k k =
      2*(Complex.normSq τ:ℂ)*(1 : Matrix ι ι ℂ) p q) :
    (residualEvaluation G (G.map star) 1 X₁ Y₁ P₁ Q₁ S₁+
      residualEvaluation G (G.map star) 1 X₂ Y₂ P₂ Q₂ S₂-
      residualEvaluation G (G.map star) 1 X₁ Y₂ P₁ Q₂ S₃-
      residualEvaluation G (G.map star) 1 X₂ Y₁ P₂ Q₁ S₄) k k =
    typeIQuadratic G W+(Complex.normSq τ:ℂ)*G.trace+
      (τ-star τ)*(∑ p,∑ q,G q p*W p q) := by
  rw [residualEvaluation_four_combination]
  simp only [contract, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.mul_one, Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply,
    Finset.sum_mul, Matrix.map_apply, hX, hY, hP, hQ, hS]
  have he (p q : ι) :
      (∑ t, ∑ s, W s q * (star (G s t) - (1 : Matrix ι ι ℂ) s t) * star (W t p)) +
        2 * (Complex.normSq τ : ℂ) * (1 : Matrix ι ι ℂ) p q -
        (∑ s, τ * (1 : Matrix ι ι ℂ) s q * star (W s p)) -
        (∑ s, W s q * (star τ * (1 : Matrix ι ι ℂ) s p)) -
        (∑ s, τ * (1 : Matrix ι ι ℂ) s q * (star τ * (1 : Matrix ι ι ℂ) s p)) =
      (∑ s, ∑ t, W s q * (star (G s t) - (1 : Matrix ι ι ℂ) s t) * star (W t p)) +
        (Complex.normSq τ : ℂ) * (1 : Matrix ι ι ℂ) p q + (τ - star τ) * W p q := by
    rw [Finset.sum_comm]
    simp only [Matrix.one_apply, mul_ite, ite_mul, mul_zero, zero_mul, mul_one, one_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, skew_star_entry hW,
      Complex.normSq_eq_conj_mul_self]
    split_ifs <;> simp_all <;> ring
  simp_rw [he]
  simp only [mul_add, Finset.sum_add_distrib]
  have hn : (∑ p, ∑ q, G q p * ((Complex.normSq τ : ℂ) * (1 : Matrix ι ι ℂ) p q)) =
      (Complex.normSq τ : ℂ) * G.trace := by
    simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, Matrix.trace, Matrix.diag]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  have hc : (∑ p, ∑ q, G q p * ((τ - star τ) * W p q)) =
      (τ - star τ) * (∑ p, ∑ q, G q p * W p q) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    ring
  rw [hn, hc]
  congr 2
  simp only [typeIQuadratic, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  ring


theorem residual_four_contact_entry_trace_zero
    (k : ι) (G W : Matrix ι ι ℂ) (hW : W.conjTranspose = -W) (τ : ℂ)
    (X₁ X₂ Y₁ Y₂ P₁ P₂ Q₁ Q₂ : ι → Matrix ι ι ℂ)
    (S₁ S₂ S₃ S₄ : ι → ι → Matrix ι ι ℂ)
    (hX : ∀ q s, X₁ q k s-X₂ q k s = W s q)
    (hY : ∀ p t, Y₁ p t k-Y₂ p t k = star (W t p))
    (hP : ∀ q s, P₁ q k s-P₂ q k s = τ*(1 : Matrix ι ι ℂ) s q)
    (hQ : ∀ p t, Q₁ p t k-Q₂ p t k = star τ*(1 : Matrix ι ι ℂ) t p)
    (hS : ∀ p q, S₁ p q k k+S₂ p q k k-S₃ p q k k-S₄ p q k k =
      2*(Complex.normSq τ:ℂ)*(1 : Matrix ι ι ℂ) p q)
    (htrace : (∑ p,∑ q,G q p*W p q) = 0) :
    (residualEvaluation G (G.map star) 1 X₁ Y₁ P₁ Q₁ S₁+
      residualEvaluation G (G.map star) 1 X₂ Y₂ P₂ Q₂ S₂-
      residualEvaluation G (G.map star) 1 X₁ Y₂ P₁ Q₂ S₃-
      residualEvaluation G (G.map star) 1 X₂ Y₁ P₂ Q₁ S₄) k k =
    typeIQuadratic G W+(Complex.normSq τ:ℂ)*G.trace := by
  rw [residual_four_contact_entry k G W hW τ X₁ X₂ Y₁ Y₂ P₁ P₂ Q₁ Q₂
    S₁ S₂ S₃ S₄ hX hY hP hQ hS,htrace,mul_zero,add_zero]

end PowerConvexity
