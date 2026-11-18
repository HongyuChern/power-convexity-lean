import PowerConvexity.Algebra.DerivativeDefectBounds
import PowerConvexity.Algebra.SpectralGapRemaindersTwo

/-! # Upper bounds for the spectral squares at the true positive gap

The leading negative square improves when the true gap decreases. Thus only
the vector error is divided by the lower gap bound; no inverse-gap error is
needed for the desired upper bound.
-/
set_option autoImplicit false
open scoped ComplexOrder
namespace PowerConvexity

theorem neg_weightedSquare_div_le_comparison_two (G : Matrix (Fin 2) (Fin 2) ℂ)
    (hGpos : G.PosSemidef) (v w : Fin 2 → ℂ) {M B ε δ κ μ : ℝ}
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hε : 0 ≤ ε)
    (hδ : 0 < δ) (hδκ : δ ≤ κ) (hκμ : κ ≤ μ)
    (hG : ∀ p q, ‖G q p‖ ≤ M) (hv : ∀ p, ‖v p‖ ≤ B) (hw : ∀ p, ‖w p‖ ≤ B)
    (hd : ∀ p, ‖v p-w p‖ ≤ ε) :
    -(weightedSquare G v/(κ:ℂ)).re ≤
      -(weightedSquare G w/(μ:ℂ)).re+(8*M*B*ε)/δ := by
  have hκ : 0 < κ := hδ.trans_le hδκ
  have hE : 0 ≤ 8*M*B*ε := by positivity
  have he := weightedSquare_sub_norm_le_two G v w hM hB hε hG hv hw hd
  have hr : (weightedSquare G w).re-(weightedSquare G v).re ≤ 8*M*B*ε := by
    calc
      _ = (weightedSquare G w-weightedSquare G v).re := by rw [Complex.sub_re]
      _ ≤ ‖weightedSquare G w-weightedSquare G v‖ := Complex.re_le_norm _
      _ = ‖weightedSquare G v-weightedSquare G w‖ := norm_sub_rev _ _
      _ ≤ _ := he
  have hh := div_le_div_of_nonneg_right hr hκ.le
  have hEdiv : (8*M*B*ε)/κ ≤ (8*M*B*ε)/δ :=
    div_le_div_of_nonneg_left hE hδ hδκ
  have hwdiv : (weightedSquare G w).re/μ ≤ (weightedSquare G w).re/κ :=
    div_le_div_of_nonneg_left (weightedSquare_re_nonneg hGpos w) hκ hκμ
  rw [sub_div] at hh
  rw [Complex.div_ofReal_re,Complex.div_ofReal_re]
  linarith

theorem two_spectral_squares_error_bound (G : Matrix (Fin 2) (Fin 2) ℂ)
    (hGpos : G.PosSemidef) (V₁ V₂ U H : Fin 2 → ℂ) {B σ δ κ μ : ℝ}
    (hB : 0 ≤ B) (hσ : 0 ≤ σ) (hδ : 0 < δ) (hδκ : δ ≤ κ) (hκμ : κ ≤ μ)
    (hG : ∀ p q, ‖G q p‖ ≤ B)
    (hV₁ : ∀ p, ‖V₁ p‖ ≤ 12*B) (hV₂ : ∀ p, ‖V₂ p‖ ≤ 12*B)
    (hU : ∀ p, ‖U p‖ ≤ 12*B) (hH : ∀ p, ‖H p‖ ≤ 12*B)
    (hd₁ : ∀ p, ‖V₁ p-U p‖ ≤ 2*B*σ) (hd₂ : ∀ p, ‖V₂ p-H p‖ ≤ 9*B*σ) :
    -(weightedSquare G V₁/(κ:ℂ)).re-(weightedSquare G V₂/(κ:ℂ)).re ≤
      -(weightedSquare G U/(μ:ℂ)).re-(weightedSquare G H/(μ:ℂ)).re+
        1056*B^3*σ/δ := by
  have h₁ := neg_weightedSquare_div_le_comparison_two G hGpos V₁ U hB
    (by positivity : 0 ≤ 12*B) (by positivity : 0 ≤ 2*B*σ) hδ hδκ hκμ hG hV₁ hU hd₁
  have h₂ := neg_weightedSquare_div_le_comparison_two G hGpos V₂ H hB
    (by positivity : 0 ≤ 12*B) (by positivity : 0 ≤ 9*B*σ) hδ hδκ hκμ hG hV₂ hH hd₂
  have he : (8*B*(12*B)*(2*B*σ))/δ+(8*B*(12*B)*(9*B*σ))/δ = 1056*B^3*σ/δ := by ring
  linarith

end PowerConvexity
