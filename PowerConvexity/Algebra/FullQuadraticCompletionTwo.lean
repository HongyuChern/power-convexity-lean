import PowerConvexity.Algebra.TypeICompletionTwo

/-! # Exact completed-square identity behind final_fullQ at zero contact

All tensors are algebraic inputs in this module. Their identification with
actual third derivatives and the neighborhood error estimate remain separate.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ComplexOrder
namespace PowerConvexity

noncomputable def contactUpperVectorTwo (W D : Matrix (Fin 2) (Fin 2) ℂ)
    (τ : ℂ) (b : ℝ) : Fin 2 → ℂ := fun p =>
  W p 1+τ*(1 : Matrix (Fin 2) (Fin 2) ℂ) p 1-(b:ℂ)*D p 1

noncomputable def contactLowerVectorTwo (W D : Matrix (Fin 2) (Fin 2) ℂ)
    (τ : ℂ) (b : ℝ) : Fin 2 → ℂ := fun p =>
  (b:ℂ)*(W p 1+τ*(1 : Matrix (Fin 2) (Fin 2) ℂ) p 1)-D p 1

noncomputable def contactFullQuadraticTwo (G W D : Matrix (Fin 2) (Fin 2) ℂ)
    (τ : ℂ) (b : ℝ) : ℂ :=
  typeIQuadraticTwo G W+(Complex.normSq τ:ℂ)*G.trace-
    (∑ s,weightedSquare G (fun p => D p s))-
    weightedSquare G (contactUpperVectorTwo W D τ b)/(1-(b:ℂ)^2)-
    weightedSquare G (contactLowerVectorTwo W D τ b)/(1-(b:ℂ)^2)

theorem contactFullQuadraticTwo_eq (W D : Matrix (Fin 2) (Fin 2) ℂ)
    (hW : W.conjTranspose = -W) (r : Fin 2 → ℂ) (τ : ℂ) (b : ℝ)
    (hμ : 1-(b:ℂ)^2 ≠ 0)
    (htrace : (∑ p,∑ q,rankOneWeightTwo r q p*W p q) = 0)
    (hD0 : ∀ p, D p 0 = W p 0+τ*(1 : Matrix (Fin 2) (Fin 2) ℂ) p 0) :
    contactFullQuadraticTwo (rankOneWeightTwo r) W D τ b =
      (Complex.normSq W.trace:ℂ)-(∑ p,∑ s,(Complex.normSq (W p s):ℂ))-
      2*weightedSquare (rankOneWeightTwo r) (contactLowerVectorTwo W D τ b)/(1-(b:ℂ)^2) := by
  have hI := typeI_rankOne_trace_zero_two W hW r htrace
  have hshift := weightedSquare_column_shift_two (rankOneWeightTwo r) W hW τ
  rw [htrace,mul_zero,add_zero] at hshift
  have hcomp := weightedSquare_completion (rankOneWeightTwo r)
    (fun p => W p 1+τ*(1 : Matrix (Fin 2) (Fin 2) ℂ) p 1) (fun p => D p 1) b hμ
  have he : (fun p => D p 0) = (fun p => W p 0+τ*(1 : Matrix (Fin 2) (Fin 2) ℂ) p 0) := funext hD0
  simp only [Fin.sum_univ_two] at hI hshift
  unfold contactFullQuadraticTwo contactUpperVectorTwo contactLowerVectorTwo
  rw [Fin.sum_univ_two,he]
  simp only [Fin.sum_univ_two]
  linear_combination hI-hshift-hcomp

theorem contactFullQuadraticTwo_nonpos (W D : Matrix (Fin 2) (Fin 2) ℂ)
    (hW : W.conjTranspose = -W) (r : Fin 2 → ℂ) (τ : ℂ) (b : ℝ)
    (hμ : 0 < 1-b^2)
    (htrace : (∑ p,∑ q,rankOneWeightTwo r q p*W p q) = 0)
    (hD0 : ∀ p, D p 0 = W p 0+τ*(1 : Matrix (Fin 2) (Fin 2) ℂ) p 0) :
    (contactFullQuadraticTwo (rankOneWeightTwo r) W D τ b).re ≤ 0 := by
  have hμc : 1-(b:ℂ)^2 ≠ 0 := by exact_mod_cast ne_of_gt hμ
  rw [contactFullQuadraticTwo_eq W D hW r τ b hμc htrace hD0]
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
  simp only [Complex.sub_re,Complex.ofReal_re,Complex.re_sum,hreal]
  have hp : 0 ≤ 2*(weightedSquare (rankOneWeightTwo r) (contactLowerVectorTwo W D τ b)).re/(1-b^2) :=
    div_nonneg (mul_nonneg (by norm_num) hsq) hμ.le
  linarith

end PowerConvexity
