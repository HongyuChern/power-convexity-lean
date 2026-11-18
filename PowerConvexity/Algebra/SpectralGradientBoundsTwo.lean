import PowerConvexity.Algebra.MatrixEntryBoundsTwo

/-! # Explicit bounds for the zeroth-order and gradient remainders -/
set_option autoImplicit false
open scoped BigOperators
namespace PowerConvexity

theorem doubleContraction_norm_le_two (G F : Matrix (Fin 2) (Fin 2) ℂ)
    {M N : ℝ} (hM : 0 ≤ M) (hG : matrixEntryBoundTwo G M)
    (hF : matrixEntryBoundTwo F N) :
    ‖∑ p,∑ q,G q p*F p q‖ ≤ 4*M*N := by
  calc
    _ ≤ ∑ p,‖∑ q,G q p*F p q‖ := norm_sum_le _ _
    _ ≤ ∑ p,∑ q,‖G q p*F p q‖ := by
      apply Finset.sum_le_sum
      intro p _
      exact norm_sum_le _ _
    _ ≤ ∑ _p : Fin 2,∑ _q : Fin 2,M*N := by
      apply Finset.sum_le_sum
      intro p _
      apply Finset.sum_le_sum
      intro q _
      rw [norm_mul]
      exact mul_le_mul (hG q p) (hF p q) (norm_nonneg _) hM
    _ = _ := by simp [Fin.sum_univ_two]; ring

noncomputable def spectralGradientCrossTwo (G : Matrix (Fin 2) (Fin 2) ℂ)
    (s a : Fin 2 → ℂ) : ℂ :=
  ∑ p,∑ q,G q p*(s p*star (a q)+a p*star (s q))

theorem spectralGradientCrossTwo_norm_le (G : Matrix (Fin 2) (Fin 2) ℂ)
    (s a : Fin 2 → ℂ) {B γ : ℝ} (hB : 0 ≤ B) (hγ : 0 ≤ γ)
    (hG : matrixEntryBoundTwo G B) (hs : ∀ p, ‖s p‖ ≤ γ) (ha : ∀ p, ‖a p‖ ≤ B) :
    ‖spectralGradientCrossTwo G s a‖ ≤ 8*B^2*γ := by
  have hF : matrixEntryBoundTwo (fun p q => s p*star (a q)+a p*star (s q)) (2*B*γ) := by
    intro p q
    calc
      _ ≤ ‖s p*star (a q)‖+‖a p*star (s q)‖ := norm_add_le _ _
      _ ≤ γ*B+B*γ := by simp only [norm_mul,norm_star]; gcongr <;> first | exact hs _ | exact ha _
      _ = _ := by ring
  exact (doubleContraction_norm_le_two G _ hB hG hF).trans (by ring_nf; rfl)

end PowerConvexity
