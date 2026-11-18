import PowerConvexity.Algebra.DimensionTwoStrictSign

/-! # A uniform quantitative version of the dimension-two sign

The constant is explicit on bounded rank-one weights; no compactness or
unproved coercivity premise is used.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators ComplexOrder
namespace PowerConvexity

theorem scalar_weighted_trace_cauchy_two (a b c d P Q X Y : ℝ)
    (hP : 0 < P) (ht : a*P+c*Q+2*b*X-2*d*Y = 0) :
    (P^2+Q^2+2*X^2+2*Y^2)*(a+c)^2 ≤
      (2*(P^2+Q^2+2*X^2+2*Y^2)-(P+Q)^2)*(a^2+c^2+2*b^2+2*d^2) := by
  let N := P^2+Q^2+2*X^2+2*Y^2
  let T := P+Q
  let v : Fin 6 → ℝ := ![a,c,b,b,d,d]
  let z : Fin 6 → ℝ := ![N-T*P,N-T*Q,-T*X,-T*X,T*Y,T*Y]
  have hN : 0 < N := by
    dsimp only [N]
    nlinarith [sq_pos_of_pos hP,sq_nonneg Q,sq_nonneg X,sq_nonneg Y]
  have hd : (∑ i, z i*v i) = N*(a+c) := by
    simp only [z,v,Fin.sum_univ_succ,Fin.sum_univ_zero,Matrix.cons_val_zero,
      Matrix.cons_val_succ,add_zero]
    dsimp only [T]
    linear_combination -(P+Q)*ht
  have hz : (∑ i, z i^2) = N*(2*N-T^2) := by
    simp only [z,Fin.sum_univ_succ,Fin.sum_univ_zero,Matrix.cons_val_zero,
      Matrix.cons_val_succ,add_zero]
    dsimp only [N,T]
    ring
  have hv : (∑ i, v i^2) = a^2+c^2+2*b^2+2*d^2 := by
    simp only [v,Fin.sum_univ_succ,Fin.sum_univ_zero,Matrix.cons_val_zero,
      Matrix.cons_val_succ,add_zero]
    ring
  have hh := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 6)) z v
  rw [hd,hz,hv] at hh
  have he : N*(N*(a+c)^2) ≤ N*((2*N-T^2)*(a^2+c^2+2*b^2+2*d^2)) := by
    nlinarith only [hh]
  change N*(a+c)^2 ≤ (2*N-T^2)*(a^2+c^2+2*b^2+2*d^2)
  exact (mul_le_mul_iff_right₀ hN).mp (by nlinarith only [he])

theorem dimensionTwo_scalar_coercive (a b c d w₁ v₁ w₂ v₂ : ℝ)
    (htrace : a*(1+w₁^2+v₁^2)+c*(1+w₂^2+v₂^2)+
      2*b*(w₁*w₂+v₁*v₂)-2*d*(v₁*w₂-w₁*v₂) = 0) :
    let s := w₁^2+v₁^2+w₂^2+v₂^2
    (2+2*s)*(a^2+c^2+2*b^2+2*d^2) ≤
      (2+2*s+s^2)*(a^2+c^2+2*b^2+2*d^2-(a+c)^2) := by
  have hh := scalar_weighted_trace_cauchy_two a b c d
    (1+w₁^2+v₁^2) (1+w₂^2+v₂^2)
    (w₁*w₂+v₁*v₂) (v₁*w₂-w₁*v₂) (by positivity) htrace
  let s := w₁^2+v₁^2+w₂^2+v₂^2
  have hN : (1+w₁^2+v₁^2)^2+(1+w₂^2+v₂^2)^2+
      2*(w₁*w₂+v₁*v₂)^2+2*(v₁*w₂-w₁*v₂)^2 = 2+2*s+s^2 := by
    dsimp only [s]
    ring
  have hT : (1+w₁^2+v₁^2)+(1+w₂^2+v₂^2) = 2+s := by
    dsimp only [s]
    ring
  rw [hN,hT] at hh
  change (2+2*s)*(a^2+c^2+2*b^2+2*d^2) ≤
    (2+2*s+s^2)*(a^2+c^2+2*b^2+2*d^2-(a+c)^2)
  nlinarith only [hh]

theorem dimensionTwo_skew_coercive (W : Matrix (Fin 2) (Fin 2) ℂ)
    (hW : W.conjTranspose = -W) (r : Fin 2 → ℂ)
    (htrace : (∑ p,∑ q,rankOneWeightTwo r q p*W p q) = 0) :
    let s := Complex.normSq (r 0)+Complex.normSq (r 1)
    (2+2*s)*(∑ p,∑ q,Complex.normSq (W p q)) ≤
      (2+2*s+s^2)*((∑ p,∑ q,Complex.normSq (W p q))-Complex.normSq W.trace) := by
  have ht := congrArg Complex.im htrace
  rw [skewMatrixTwo_representation W hW,rankOneWeightTwo_trace_im] at ht
  have hh := dimensionTwo_scalar_coercive (W 0 0).im (W 0 1).im (W 1 1).im (W 0 1).re
    (r 0).re (r 0).im (r 1).re (r 1).im ht
  rw [skewMatrixTwo_representation W hW]
  simp [Matrix.trace,Matrix.diag,skewMatrixTwo,Fin.sum_univ_two,Complex.normSq_apply]
  dsimp only at hh
  nlinarith only [hh]

theorem dimensionTwo_skew_uniform_coercive (W : Matrix (Fin 2) (Fin 2) ℂ)
    (hW : W.conjTranspose = -W) (r : Fin 2 → ℂ)
    (htrace : (∑ p,∑ q,rankOneWeightTwo r q p*W p q) = 0)
    {R : ℝ} (hR : Complex.normSq (r 0)+Complex.normSq (r 1) ≤ R) :
    0 < 2/(2+2*R+R^2) ∧
      (2/(2+2*R+R^2))*(∑ p,∑ q,Complex.normSq (W p q)) ≤
        (∑ p,∑ q,Complex.normSq (W p q))-Complex.normSq W.trace := by
  let s := Complex.normSq (r 0)+Complex.normSq (r 1)
  let N := ∑ p,∑ q,Complex.normSq (W p q)
  let Q := N-Complex.normSq W.trace
  have hs : 0 ≤ s := add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  have hRN : 0 ≤ R := hs.trans hR
  have hD : 0 < 2+2*R+R^2 := by positivity
  have hN : 0 ≤ N := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  have hQ : 0 ≤ Q := sub_nonneg.mpr (dimensionTwo_skew_sign W hW r htrace)
  have hh := dimensionTwo_skew_coercive W hW r htrace
  change (2+2*s)*N ≤ (2+2*s+s^2)*Q at hh
  have hden : 2+2*s+s^2 ≤ 2+2*R+R^2 := by nlinarith
  have hsmall : 2*N ≤ (2+2*s)*N := by nlinarith [mul_nonneg hs hN]
  have hlarge := mul_le_mul_of_nonneg_right hden hQ
  refine ⟨div_pos (by norm_num) hD,?_⟩
  change (2/(2+2*R+R^2))*N ≤ Q
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hD).mpr
  nlinarith only [hsmall,hh,hlarge]

end PowerConvexity
