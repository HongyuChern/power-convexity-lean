import PowerConvexity.Algebra.WeightedSquares

/-! # The Type I and shifted-column identities in arbitrary finite dimension

Only identities are proved here. The dimension-two sign is not generalized.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators ComplexOrder
namespace PowerConvexity
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def rankOneWeight (r : ι → ℂ) : Matrix ι ι ℂ :=
  1 + Matrix.vecMulVec r (star r)

noncomputable def typeIQuadratic (G W : Matrix ι ι ℂ) : ℂ :=
  ∑ p, ∑ q, ∑ s, ∑ t,
    G q p * W s q * (star (G s t) - (1 : Matrix ι ι ℂ) s t) * star (W t p)

theorem skew_star_entry {W : Matrix ι ι ℂ} (hW : W.conjTranspose = -W) (p q : ι) :
    star (W p q) = -W q p := by
  exact congrArg (fun M : Matrix ι ι ℂ => M q p) hW

theorem weightedSquare_column_shift (G W : Matrix ι ι ℂ)
    (hW : W.conjTranspose = -W) (τ : ℂ) :
    (∑ s, weightedSquare G (fun p => W p s + τ * (1 : Matrix ι ι ℂ) p s)) =
      (∑ s, weightedSquare G (fun p => W p s)) +
      (Complex.normSq τ : ℂ) * G.trace +
      (star τ - τ) * (∑ p, ∑ q, G q p * W p q) := by
  have he (s p q : ι) :
      G q p * (W p s + τ * (1 : Matrix ι ι ℂ) p s) *
        star (W q s + τ * (1 : Matrix ι ι ℂ) q s) =
      G q p * W p s * star (W q s) +
      star τ * G q p * W p s * (1 : Matrix ι ι ℂ) q s -
      τ * G q p * W s q * (1 : Matrix ι ι ℂ) p s +
      (Complex.normSq τ : ℂ) * G q p *
        (1 : Matrix ι ι ℂ) p s * (1 : Matrix ι ι ℂ) q s := by
    simp only [star_add, star_mul, skew_star_entry hW, Complex.normSq_eq_conj_mul_self]
    have h1 : star ((1 : Matrix ι ι ℂ) q s) = (1 : Matrix ι ι ℂ) q s := by
      simp [Matrix.one_apply]
    rw [h1]
    change _ = _ + _ - _ + (star τ * τ) * _ * _ * _
    ring
  simp only [weightedSquare, he, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Finset.sum_ite_irrel]
  simp only [mul_assoc, ← Finset.mul_sum, Matrix.trace, Matrix.diag]
  rw [show (∑ s, ∑ p, G s p * W p s) = ∑ p, ∑ q, G q p * W p q from Finset.sum_comm]
  simp only [Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, ← Finset.mul_sum]
  ring

theorem rankOneWeight_star_sub_one (r : ι → ℂ) (s t : ι) :
    star (rankOneWeight r s t) - (1 : Matrix ι ι ℂ) s t = star (r s) * r t := by
  simp only [rankOneWeight, Matrix.add_apply, Matrix.vecMulVec, Matrix.of_apply, Pi.star_apply,
    star_add, star_mul, star_star]
  have h1 : star ((1 : Matrix ι ι ℂ) s t) = (1 : Matrix ι ι ℂ) s t := by
    simp [Matrix.one_apply]
  rw [h1]
  ring

theorem sum_four_middle_rotate (f : ι → ι → ι → ι → ℂ) :
    (∑ p, ∑ q, ∑ s, ∑ t, f p q s t) = ∑ s, ∑ q, ∑ t, ∑ p, f p q s t := by
  calc
    _ = ∑ q, ∑ s, ∑ p, ∑ t, f p q s t := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q _
      exact Finset.sum_comm
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro q _
      exact Finset.sum_comm

theorem rankOne_fourfold_trace_square (W : Matrix ι ι ℂ) (r : ι → ℂ) :
    (∑ p, ∑ q, ∑ s, ∑ t,
      r q * star (r p) * W s q * (star (r s) * r t) * star (W t p)) = (Complex.normSq (∑ p, ∑ q, r q * star (r p) * W p q) : ℂ) := by
  let T : ℂ := ∑ p, ∑ q, ∑ s, ∑ t,
    r q * star (r p) * W s q * (star (r s) * r t) * star (W t p)
  change T = _
  rw [Complex.normSq_eq_conj_mul_self]
  simp only [map_sum, map_mul, Complex.star_def, map_star, star_star,
    Finset.sum_mul, Finset.mul_sum]
  rw [show T = ∑ s, ∑ q, ∑ t, ∑ p,
      r q * star (r p) * W s q * (star (r s) * r t) * star (W t p)
    from sum_four_middle_rotate _]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro p _
  simp only [Complex.star_def, map_mul, starRingEnd_self_apply]
  ring

theorem rankOne_trace_constraint (W : Matrix ι ι ℂ) (r : ι → ℂ)
    (htrace : (∑ p, ∑ q, rankOneWeight r q p * W p q) = 0) : (∑ p, ∑ q, r q * star (r p) * W p q) = -W.trace := by
  simp only [rankOneWeight, Matrix.add_apply, Matrix.vecMulVec, Matrix.of_apply, Pi.star_apply,
    add_mul, Finset.sum_add_distrib] at htrace
  simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at htrace
  change W.trace + _ = 0 at htrace
  linear_combination htrace

/-- The two summands in frozen (3.12.1): the rank-one fourth-order term
is the squared rank-one trace. No dimension or skewness is required here. -/
theorem typeI_rankOne_decomposition (W : Matrix ι ι ℂ) (r : ι → ℂ) :
    typeIQuadratic (rankOneWeight r) W =
      (∑ s, weightedSquare (rankOneWeight r) (fun p => W p s)) -
      (∑ s, ∑ p, (Complex.normSq (W p s) : ℂ)) +
      (Complex.normSq (∑ p, ∑ q, r q * star (r p) * W p q) : ℂ) := by
  let T : ℂ := ∑ p, ∑ q, ∑ s, ∑ t,
    r q * star (r p) * W s q * (star (r s) * r t) * star (W t p)
  have ht : T = (Complex.normSq (∑ p, ∑ q, r q * star (r p) * W p q) : ℂ) :=
    rankOne_fourfold_trace_square W r
  have hw : (∑ s, weightedSquare (rankOneWeight r) (fun p => W p s)) =
      (∑ s, ∑ p, (Complex.normSq (W p s) : ℂ)) +
      ∑ s, ∑ p, ∑ q, r q * star (r p) * W p s * star (W q s) := by
    simp only [weightedSquare, rankOneWeight, Matrix.add_apply, Matrix.vecMulVec, Matrix.of_apply,
      Pi.star_apply, add_mul, Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro p _
    simp [Matrix.one_apply, ite_mul, Complex.mul_conj, Complex.star_def]
  have hi : typeIQuadratic (rankOneWeight r) W =
      (∑ s, ∑ p, ∑ q, r q * star (r p) * W p s * star (W q s)) + T := by
    simp only [typeIQuadratic, rankOneWeight_star_sub_one]
    simp only [rankOneWeight, Matrix.add_apply, Matrix.vecMulVec, Matrix.of_apply, Pi.star_apply,
      add_mul, Finset.sum_add_distrib]
    change _ + T = _ + T
    congr 1
    simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    ring
  rw [hi, hw, ht]
  ring

theorem typeI_rankOne_trace_zero (W : Matrix ι ι ℂ) (r : ι → ℂ)
    (htrace : (∑ p, ∑ q, rankOneWeight r q p * W p q) = 0) :
    typeIQuadratic (rankOneWeight r) W =
      (Complex.normSq W.trace : ℂ) +
      (∑ s, weightedSquare (rankOneWeight r) (fun p => W p s)) -
      (∑ p, ∑ s, (Complex.normSq (W p s) : ℂ)) := by
  have ht := rankOne_trace_constraint W r htrace
  rw [typeI_rankOne_decomposition, ht, Complex.normSq_neg]
  rw [Finset.sum_comm (f := fun s p => (Complex.normSq (W p s) : ℂ))]
  ring

end PowerConvexity
