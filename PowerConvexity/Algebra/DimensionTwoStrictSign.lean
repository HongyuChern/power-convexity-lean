import PowerConvexity.Algebra.TypeICompletionTwo

/-! # Strictness of the dimension-two skew quadratic form

This strengthens the frozen algebraic sign on the weighted-trace-zero subspace.
It does not by itself propagate a repeated spectral zero.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators ComplexOrder
namespace PowerConvexity

theorem dimensionTwo_scalar_strict_sign (a b c d w₁ v₁ w₂ v₂ : ℝ)
    (htrace : a*(1+w₁^2+v₁^2)+c*(1+w₂^2+v₂^2)+
      2*b*(w₁*w₂+v₁*v₂)-2*d*(v₁*w₂-w₁*v₂) = 0)
    (hne : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 ∨ d ≠ 0) : a*c < b^2+d^2 := by
  let P := 1+w₁^2+v₁^2
  let X := w₁*w₂+v₁*v₂
  let Y := v₁*w₂-w₁*v₂
  let G := 1+w₁^2+v₁^2+w₂^2+v₂^2
  have hP : 0 < P := by dsimp [P]; positivity
  have hG : 0 < G := by dsimp [G]; positivity
  have hid : P^2*(b^2+d^2-a*c) = (P*b+c*X)^2+(P*d-c*Y)^2+c^2*G := by
    dsimp [P,X,Y,G]
    linear_combination -(c*(1+w₁^2+v₁^2))*htrace
  have hle := dimensionTwo_scalar_sign a b c d w₁ v₁ w₂ v₂ htrace
  by_contra hn
  have heq : b^2+d^2-a*c = 0 := by linarith
  rw [heq,mul_zero] at hid
  have hcg : c^2*G ≤ 0 := by nlinarith [sq_nonneg (P*b+c*X),sq_nonneg (P*d-c*Y)]
  have hc2 : c^2 ≤ 0 := by
    by_contra hn
    have hh := mul_pos (lt_of_not_ge hn) hG
    linarith
  have hc : c = 0 := by nlinarith [sq_nonneg c]
  simp only [hc,mul_zero,sub_zero] at heq
  have hb : b = 0 := by nlinarith [sq_nonneg d]
  have hd : d = 0 := by nlinarith [sq_nonneg b]
  have haP : a*P = 0 := by
    dsimp [P]
    simpa only [hc,hb,hd,zero_mul,mul_zero,zero_add,add_zero,sub_zero] using htrace
  have ha : a = 0 := (mul_eq_zero.mp haP).resolve_right hP.ne'
  rcases hne with h | h | h | h <;> contradiction

theorem dimensionTwo_skew_strict_sign (W : Matrix (Fin 2) (Fin 2) ℂ)
    (hW : W.conjTranspose = -W) (r : Fin 2 → ℂ)
    (htrace : (∑ p,∑ q,rankOneWeightTwo r q p*W p q) = 0)
    (hne : W ≠ 0) : Complex.normSq W.trace < ∑ p,∑ s,Complex.normSq (W p s) := by
  have ht := congrArg Complex.im htrace
  rw [skewMatrixTwo_representation W hW,rankOneWeightTwo_trace_im] at ht
  have hn : (W 0 0).im ≠ 0 ∨ (W 0 1).im ≠ 0 ∨ (W 1 1).im ≠ 0 ∨ (W 0 1).re ≠ 0 := by
    by_contra h
    push_neg at h
    apply hne
    rw [skewMatrixTwo_representation W hW]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [skewMatrixTwo,h.1,h.2.1,h.2.2.1,h.2.2.2]
  have hs := dimensionTwo_scalar_strict_sign (W 0 0).im (W 0 1).im (W 1 1).im (W 0 1).re
    (r 0).re (r 0).im (r 1).re (r 1).im ht hn
  rw [skewMatrixTwo_representation W hW]
  simp [Matrix.trace,Matrix.diag,skewMatrixTwo,Fin.sum_univ_two,Complex.normSq_apply]
  nlinarith

theorem dimensionTwo_skew_equality_iff_zero (W : Matrix (Fin 2) (Fin 2) ℂ)
    (hW : W.conjTranspose = -W) (r : Fin 2 → ℂ)
    (htrace : (∑ p,∑ q,rankOneWeightTwo r q p*W p q) = 0) :
    Complex.normSq W.trace = (∑ p,∑ s,Complex.normSq (W p s)) ↔ W = 0 := by
  constructor
  · intro he
    by_contra hn
    exact (ne_of_lt (dimensionTwo_skew_strict_sign W hW r htrace hn)) he
  · intro he
    simp [he,Matrix.trace,Matrix.diag]

end PowerConvexity
