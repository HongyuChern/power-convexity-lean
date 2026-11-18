import PowerConvexity.Algebra.QuadraticCompletionDefectTwo
import PowerConvexity.Algebra.DerivativeDefectBounds

/-! # Quantitative upper bound for the completed quadratic form off contact -/
set_option autoImplicit false
open scoped BigOperators ComplexOrder
namespace PowerConvexity

theorem contactFullQuadraticTwo_le_defect_norm (W D : Matrix (Fin 2) (Fin 2) ℂ)
    (hW : W.conjTranspose = -W) (r : Fin 2 → ℂ) (τ : ℂ) (b : ℝ)
    (hμ : 0 < 1-b^2)
    (htrace : (∑ p,∑ q,rankOneWeightTwo r q p*W p q) = 0)
    {M B ε : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B) (hε : 0 ≤ ε)
    (hG : ∀ p q, ‖rankOneWeightTwo r q p‖ ≤ M)
    (hX : ∀ p, ‖W p 0+τ*(1 : Matrix (Fin 2) (Fin 2) ℂ) p 0‖ ≤ B)
    (hD : ∀ p, ‖D p 0‖ ≤ B)
    (hd : ∀ p, ‖D p 0-(W p 0+τ*(1 : Matrix (Fin 2) (Fin 2) ℂ) p 0)‖ ≤ ε) :
    (contactFullQuadraticTwo (rankOneWeightTwo r) W D τ b).re ≤ 8*M*B*ε := by
  refine (contactFullQuadraticTwo_le_defect W D hW r τ b hμ htrace).trans ?_
  refine (Complex.re_le_norm _).trans ?_
  apply weightedSquare_sub_norm_le_two _ _ _ hM hB hε hG hX hD
  intro p
  rw [norm_sub_rev]
  exact hd p

end PowerConvexity
