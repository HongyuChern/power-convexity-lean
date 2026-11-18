import PowerConvexity.Algebra.WeightedSquares

/-! # Exact rank-one Type I reduction in dimension two -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators ComplexOrder
namespace PowerConvexity

noncomputable def typeIQuadraticTwo (G W : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  ∑ p, ∑ q, ∑ s, ∑ t,
    G q p*W s q*(star (G s t)-(1 : Matrix (Fin 2) (Fin 2) ℂ) s t)*star (W t p)

/-- This intermediate identity keeps the rank-one trace term before using
its vanishing, so the source of the squared trace is explicit. -/
theorem typeI_rankOne_decomposition_two (W : Matrix (Fin 2) (Fin 2) ℂ)
    (hW : W.conjTranspose = -W) (r : Fin 2 → ℂ) :
    typeIQuadraticTwo (rankOneWeightTwo r) W =
      (∑ s, weightedSquare (rankOneWeightTwo r) (fun p => W p s)) -
      (∑ p, ∑ s, (Complex.normSq (W p s):ℂ)) +
      (Complex.normSq (∑ p, ∑ q,
        (rankOneWeightTwo r q p-(1 : Matrix (Fin 2) (Fin 2) ℂ) q p)*W p q):ℂ) := by
  rw [skewMatrixTwo_representation W hW]
  apply Complex.ext <;>
    simp [typeIQuadraticTwo,weightedSquare,rankOneWeightTwo,skewMatrixTwo,
      Fin.sum_univ_two,Matrix.vecMulVec,Matrix.one_apply,Complex.star_def,
      Complex.normSq_apply,Complex.mul_re,Complex.mul_im] <;> ring

theorem typeI_rankOne_trace_zero_two (W : Matrix (Fin 2) (Fin 2) ℂ)
    (hW : W.conjTranspose = -W) (r : Fin 2 → ℂ)
    (htrace : (∑ p, ∑ q, rankOneWeightTwo r q p*W p q) = 0) :
    typeIQuadraticTwo (rankOneWeightTwo r) W =
      (Complex.normSq W.trace:ℂ) +
      (∑ s, weightedSquare (rankOneWeightTwo r) (fun p => W p s)) -
      (∑ p, ∑ s, (Complex.normSq (W p s):ℂ)) := by
  have ht : (∑ p, ∑ q,
      (rankOneWeightTwo r q p-(1 : Matrix (Fin 2) (Fin 2) ℂ) q p)*W p q) = -W.trace := by
    simp only [sub_mul,Finset.sum_sub_distrib]
    rw [htrace]
    simp [Matrix.trace,Matrix.diag,Fin.sum_univ_two]
  rw [typeI_rankOne_decomposition_two W hW r,ht]
  simp only [Complex.normSq_neg]
  ring

/-- The shift by tau*I contributes only the weighted trace constraint and
|tau|² trace(G). No reality assumption on tau is needed here. -/
theorem weightedSquare_column_shift_two (G W : Matrix (Fin 2) (Fin 2) ℂ)
    (hW : W.conjTranspose = -W) (τ : ℂ) :
    (∑ s, weightedSquare G (fun p => W p s+τ*(1 : Matrix (Fin 2) (Fin 2) ℂ) p s)) =
      (∑ s, weightedSquare G (fun p => W p s)) +
      (Complex.normSq τ:ℂ)*G.trace+
      (star τ-τ)*(∑ p, ∑ q, G q p*W p q) := by
  rw [skewMatrixTwo_representation W hW]
  apply Complex.ext <;>
    simp [weightedSquare,skewMatrixTwo,Fin.sum_univ_two,Matrix.trace,Matrix.diag,
      Matrix.one_apply,Complex.star_def,Complex.normSq_apply,Complex.mul_re,Complex.mul_im] <;> ring

end PowerConvexity
