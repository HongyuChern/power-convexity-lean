import PowerConvexity.Algebra.FullQuadraticCompletionTwo

/-! # Completed squares with the first-column defect retained -/
set_option autoImplicit false
open scoped BigOperators ComplexOrder
namespace PowerConvexity

theorem contactFullQuadraticTwo_eq_with_defect (W D : Matrix (Fin 2) (Fin 2) ℂ)
    (hW : W.conjTranspose = -W) (r : Fin 2 → ℂ) (τ : ℂ) (b : ℝ)
    (hμ : 1-(b:ℂ)^2 ≠ 0)
    (htrace : (∑ p,∑ q,rankOneWeightTwo r q p*W p q) = 0) :
    contactFullQuadraticTwo (rankOneWeightTwo r) W D τ b =
      (Complex.normSq W.trace:ℂ)-(∑ p,∑ s,(Complex.normSq (W p s):ℂ))-
      2*weightedSquare (rankOneWeightTwo r) (contactLowerVectorTwo W D τ b)/(1-(b:ℂ)^2)+
      weightedSquare (rankOneWeightTwo r) (fun p => W p 0+τ*(1 : Matrix (Fin 2) (Fin 2) ℂ) p 0)-
      weightedSquare (rankOneWeightTwo r) (fun p => D p 0) := by
  have hI := typeI_rankOne_trace_zero_two W hW r htrace
  have hshift := weightedSquare_column_shift_two (rankOneWeightTwo r) W hW τ
  rw [htrace,mul_zero,add_zero] at hshift
  have hcomp := weightedSquare_completion (rankOneWeightTwo r)
    (fun p => W p 1+τ*(1 : Matrix (Fin 2) (Fin 2) ℂ) p 1) (fun p => D p 1) b hμ
  simp only [Fin.sum_univ_two] at hI hshift
  unfold contactFullQuadraticTwo contactUpperVectorTwo contactLowerVectorTwo
  simp only [Fin.sum_univ_two]
  linear_combination hI-hshift-hcomp

theorem contactFullQuadraticTwo_le_defect (W D : Matrix (Fin 2) (Fin 2) ℂ)
    (hW : W.conjTranspose = -W) (r : Fin 2 → ℂ) (τ : ℂ) (b : ℝ)
    (hμ : 0 < 1-b^2)
    (htrace : (∑ p,∑ q,rankOneWeightTwo r q p*W p q) = 0) :
    (contactFullQuadraticTwo (rankOneWeightTwo r) W D τ b).re ≤
      (weightedSquare (rankOneWeightTwo r) (fun p => W p 0+τ*(1 : Matrix (Fin 2) (Fin 2) ℂ) p 0)-
       weightedSquare (rankOneWeightTwo r) (fun p => D p 0)).re := by
  have hμc : 1-(b:ℂ)^2 ≠ 0 := by exact_mod_cast ne_of_gt hμ
  rw [contactFullQuadraticTwo_eq_with_defect W D hW r τ b hμc htrace]
  have hsign := dimensionTwo_skew_sign W hW r htrace
  have hG : (rankOneWeightTwo r).PosSemidef :=
    Matrix.PosSemidef.add Matrix.PosSemidef.one (Matrix.posSemidef_vecMulVec_self_star r)
  have hsq := weightedSquare_re_nonneg hG (contactLowerVectorTwo W D τ b)
  have hreal : (2*weightedSquare (rankOneWeightTwo r) (contactLowerVectorTwo W D τ b)/
      (1-(b:ℂ)^2)).re =
      2*(weightedSquare (rankOneWeightTwo r) (contactLowerVectorTwo W D τ b)).re/(1-b^2) := by
    rw [show 1-(b:ℂ)^2 = ((1-b^2:ℝ):ℂ) by push_cast; rfl]
    rw [Complex.div_ofReal_re]
    norm_num [Complex.mul_re]
  simp only [Complex.sub_re,Complex.add_re,Complex.ofReal_re,Complex.re_sum,hreal]
  have hp := div_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hsq) hμ.le
  linarith

end PowerConvexity
