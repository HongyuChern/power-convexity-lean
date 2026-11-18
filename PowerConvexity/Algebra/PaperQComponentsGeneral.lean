import PowerConvexity.Algebra.TypeICompletionGeneral
import PowerConvexity.Algebra.PaperQDecompositionGeneral

/-! # Independently exported finite-dimensional Q1, Q42 and Q66 components

The inverse-Hessian row order is G[q,p]. This retains the conjugation correction
already recorded for the frozen text; it proves identities, not a higher-dimensional sign.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace PowerConvexity
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem paper_Q1_split (W : Matrix ι ι ℂ) (r : ι → ℂ) :
    typeIQuadratic (rankOneWeight r) W =
      (∑ p, ∑ q, ∑ s, ∑ t,
        (1:Matrix ι ι ℂ) q p * W s q * (star (r s)*r t) * star (W t p)) +
      (∑ p, ∑ q, ∑ s, ∑ t,
        r q*star (r p)*W s q*(star (r s)*r t)*star (W t p)) := by
  simp only [typeIQuadratic, rankOneWeight_star_sub_one]
  simp only [rankOneWeight,
    Matrix.add_apply, Matrix.vecMulVec, Matrix.of_apply, Pi.star_apply,
    add_mul, Finset.sum_add_distrib]

theorem paper_Q11_trace_square (W : Matrix ι ι ℂ) (r : ι → ℂ)
    (htrace : (∑ p, ∑ q, rankOneWeight r q p*W p q) = 0) :
    (∑ p, ∑ q, ∑ s, ∑ t,
      r q*star (r p)*W s q*(star (r s)*r t)*star (W t p)) =
      (Complex.normSq W.trace:ℂ) := by
  rw [rankOne_fourfold_trace_square, rankOne_trace_constraint W r htrace, Complex.normSq_neg]

theorem paper_Q12_Q13_split (W : Matrix ι ι ℂ) (r : ι → ℂ) (i : ι) :
    (∑ p, ∑ q, ∑ s, ∑ t,
      (1:Matrix ι ι ℂ) q p*W s q*(star (r s)*r t)*star (W t p)) =
      (∑ s ∈ Finset.univ.erase i, ∑ p, ∑ q, r q*star (r p)*W p s*star (W q s)) +
      (∑ p, ∑ q, r q*star (r p)*W p i*star (W q i)) := by
  rw [Finset.sum_erase_add Finset.univ
    (fun s => ∑ p, ∑ q, r q*star (r p)*W p s*star (W q s)) (Finset.mem_univ i)]
  simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  ring

theorem rankOne_weightedColumn_decomposition (W : Matrix ι ι ℂ) (r : ι → ℂ) (i : ι) :
    weightedSquare (rankOneWeight r) (fun p => W p i) =
      (∑ p, (Complex.normSq (W p i):ℂ)) +
      (∑ p, ∑ q, r q*star (r p)*W p i*star (W q i)) := by
  simp only [weightedSquare, rankOneWeight, Matrix.add_apply, Matrix.vecMulVec,
    Matrix.of_apply, Pi.star_apply, add_mul, Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  simp [Matrix.one_apply, ite_mul, Complex.mul_conj, Complex.star_def]

theorem paper_Q13_Q421_cancel (W : Matrix ι ι ℂ) (r : ι → ℂ) (i : ι) :
    (∑ p, ∑ q, r q*star (r p)*W p i*star (W q i)) -
      weightedSquare (rankOneWeight r) (fun p => W p i) =
      -(∑ p, (Complex.normSq (W p i):ℂ)) := by
  rw [rankOne_weightedColumn_decomposition]
  ring

theorem weightedSquare_basis (G : Matrix ι ι ℂ) (i : ι) :
    weightedSquare G (fun p => (1:Matrix ι ι ℂ) p i) = G i i := by
  simp [weightedSquare, Matrix.one_apply]

theorem paper_Q42_split (G W : Matrix ι ι ℂ) (τ : ℂ) (i : ι) :
    -weightedSquare G (fun p => W p i+τ*(1:Matrix ι ι ℂ) p i) =
      -weightedSquare G (fun p => W p i) -
      (star τ*weightedPair G (fun p => W p i) (fun p => (1:Matrix ι ι ℂ) p i) +
        τ*weightedPair G (fun p => (1:Matrix ι ι ℂ) p i) (fun p => W p i)) -
      (Complex.normSq τ:ℂ)*G i i := by
  have h := weightedSquare_three_term G (fun p => W p i) (fun _ => 0)
    (fun p => (1:Matrix ι ι ℂ) p i) τ 0
  simp only [Complex.ofReal_zero, zero_mul, sub_zero, zero_pow (by norm_num : 2 ≠ 0),
    weightedSquare_basis] at h
  rw [h]
  ring

theorem paper_Q422_complement (G W : Matrix ι ι ℂ) (hW : W.conjTranspose = -W)
    (τ : ℂ) (i : ι) (htrace : (∑ p, ∑ q, G q p*W p q) = 0) :
    -(star τ*weightedPair G (fun p => W p i) (fun p => (1:Matrix ι ι ℂ) p i) +
      τ*weightedPair G (fun p => (1:Matrix ι ι ℂ) p i) (fun p => W p i)) =
      ∑ s ∈ Finset.univ.erase i,
        (star τ*weightedPair G (fun p => W p s) (fun p => (1:Matrix ι ι ℂ) p s) +
          τ*weightedPair G (fun p => (1:Matrix ι ι ℂ) p s) (fun p => W p s)) := by
  let F (s : ι) := star τ*weightedPair G (fun p => W p s) (fun p => (1:Matrix ι ι ℂ) p s) +
    τ*weightedPair G (fun p => (1:Matrix ι ι ℂ) p s) (fun p => W p s)
  have hs : ∑ s, F s = 0 := by
    have h := weightedSquare_column_shift G W hW τ
    rw [htrace, mul_zero, add_zero] at h
    have he (s : ι) : weightedSquare G (fun p => W p s+τ*(1:Matrix ι ι ℂ) p s) =
        weightedSquare G (fun p => W p s)+F s+(Complex.normSq τ:ℂ)*G s s := by
      have hh := paper_Q42_split G W τ s
      change -_ = -_ - F s - _ at hh
      linear_combination -hh
    simp_rw [he, Finset.sum_add_distrib, ← Finset.mul_sum] at h
    change _ + _ + (Complex.normSq τ:ℂ)*G.trace = _ at h
    linear_combination h
  have he := Finset.sum_erase_add Finset.univ F (Finset.mem_univ i)
  change -F i = _
  change -F i = ∑ s ∈ Finset.univ.erase i, F s
  rw [hs] at he
  linear_combination -he

theorem paper_Q66_initial_simplify (G : Matrix ι ι ℂ) (τ : ℂ) (d : ι → ℝ) (i : ι)
    (hμ : ∀ s, s ≠ i → 1-(d s:ℂ)^2 ≠ 0) :
    (Complex.normSq τ:ℂ)*G.trace -
      (Complex.normSq τ:ℂ)*(∑ s ∈ Finset.univ.erase i, G s s/(1-(d s:ℂ)^2)) -
      (Complex.normSq τ:ℂ)*G i i =
    -(Complex.normSq τ:ℂ)*(∑ s ∈ Finset.univ.erase i, (d s:ℂ)^2*G s s/(1-(d s:ℂ)^2)) := by
  have htr : G.trace = (∑ s ∈ Finset.univ.erase i, G s s)+G i i :=
    (Finset.sum_erase_add Finset.univ (fun s => G s s) (Finset.mem_univ i)).symm
  rw [htr]
  have he : (∑ s ∈ Finset.univ.erase i, G s s)-
      (∑ s ∈ Finset.univ.erase i, G s s/(1-(d s:ℂ)^2)) =
      -(∑ s ∈ Finset.univ.erase i, (d s:ℂ)^2*G s s/(1-(d s:ℂ)^2)) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro s hs
    simpa only [neg_div, neg_mul] using
      paper_Q64_Q66_simplify (G s s) (d s) (hμ s (Finset.ne_of_mem_erase hs))
  linear_combination (Complex.normSq τ:ℂ)*he


/-- The separately exported Q1 components feed the general contact identity. -/
theorem paper_typeI_from_numbered_components (W : Matrix ι ι ℂ) (r : ι → ℂ) (i : ι)
    (htrace : (∑ p, ∑ q, rankOneWeight r q p*W p q) = 0) :
    typeIQuadratic (rankOneWeight r) W =
      (Complex.normSq W.trace:ℂ) +
      (∑ s, weightedSquare (rankOneWeight r) (fun p => W p s)) -
      (∑ p, ∑ s, (Complex.normSq (W p s):ℂ)) := by
  rw [paper_Q1_split, paper_Q11_trace_square W r htrace, paper_Q12_Q13_split W r i,
    Finset.sum_erase_add Finset.univ
      (fun s => ∑ p, ∑ q, r q*star (r p)*W p s*star (W q s)) (Finset.mem_univ i)]
  simp_rw [rankOne_weightedColumn_decomposition, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun s p => (Complex.normSq (W p s):ℂ))]
  ring

end PowerConvexity
