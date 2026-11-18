import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Algebra of the parallel-boundary curvature formula

These are pointwise scalar and diagonal-form estimates. They do not assert
that a domain has a smooth normal map, nor identify its geometric shape
operator. In particular, a zero real principal curvature stays zero.
The paired quadratic-form estimate is the algebra needed to preserve a
strict Levi lower bound without assuming every real curvature is positive.
-/
set_option autoImplicit false
open Finset
namespace PowerConvexity

theorem parallel_curvature_zero_iff {κ t r : ℝ}
    (hκ : 0 ≤ κ) (ht : 0 < t) (hr : 0 ≤ r) :
    κ / (t+r*κ) = 0 ↔ κ = 0 := by
  have hd : 0 < t+r*κ := add_pos_of_pos_of_nonneg ht (mul_nonneg hr hκ)
  simp only [div_eq_zero_iff,ne_of_gt hd,or_false]

theorem parallel_curvature_lower_bound {κ M t r : ℝ}
    (hκ : 0 ≤ κ) (hκM : κ ≤ M) (ht : 0 < t) (hr : 0 ≤ r) :
    κ/(t+r*M) ≤ κ/(t+r*κ) := by
  have hd : 0 < t+r*κ := add_pos_of_pos_of_nonneg ht (mul_nonneg hr hκ)
  have hdM : 0 < t+r*M := add_pos_of_pos_of_nonneg ht (mul_nonneg hr (hκ.trans hκM))
  apply (div_le_div_iff₀ hdM hd).mpr
  nlinarith [mul_nonneg (mul_nonneg hκ hr) (sub_nonneg.mpr hκM)]

theorem parallel_levi_diagonal_lower_bound {ι : Type*} [Fintype ι]
    (κ v w : ι → ℝ) {M t r ℓ : ℝ} (hM : 0 ≤ M) (ht : 0 < t) (hr : 0 ≤ r)
    (hκ : ∀ i, 0 ≤ κ i) (hκM : ∀ i, κ i ≤ M)
    (hlower : ℓ ≤ ∑ i, κ i*((v i)^2+(w i)^2)) :
    ℓ/(t+r*M) ≤ ∑ i, (κ i/(t+r*κ i))*((v i)^2+(w i)^2) := by
  have hd : 0 < t+r*M := add_pos_of_pos_of_nonneg ht (mul_nonneg hr hM)
  calc
    ℓ/(t+r*M) ≤ (∑ i, κ i*((v i)^2+(w i)^2))/(t+r*M) :=
      div_le_div_of_nonneg_right hlower hd.le
    _ = ∑ i, (κ i/(t+r*M))*((v i)^2+(w i)^2) := by
      simp only [div_eq_mul_inv, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ _ := Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_right (parallel_curvature_lower_bound (hκ i) (hκM i) ht hr)
        (add_nonneg (sq_nonneg _) (sq_nonneg _)))

theorem parallel_levi_diagonal_uniform_lower_bound {ι : Type*} [Fintype ι]
    (κ v w : ι → ℝ) {M R t ℓ : ℝ} (hM : 0 ≤ M) (hR : 0 ≤ R)
    (ht : 0 < t) (ht1 : t ≤ 1) (hℓ : 0 ≤ ℓ)
    (hκ : ∀ i, 0 ≤ κ i) (hκM : ∀ i, κ i ≤ M)
    (hlower : ℓ ≤ ∑ i, κ i*((v i)^2+(w i)^2)) :
    ℓ/(1+R*M) ≤ ∑ i, (κ i/(t+(1-t)*R*κ i))*((v i)^2+(w i)^2) := by
  have hr : 0 ≤ (1-t)*R := mul_nonneg (sub_nonneg.mpr ht1) hR
  have hd : 0 < t+(1-t)*R*M := add_pos_of_pos_of_nonneg ht (mul_nonneg hr hM)
  have hdmax : 0 < 1+R*M := add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hR hM)
  have hdle : t+(1-t)*R*M ≤ 1+R*M := by
    nlinarith [mul_nonneg ht.le (mul_nonneg hR hM)]
  calc
    ℓ/(1+R*M) ≤ ℓ/(t+(1-t)*R*M) := by
      apply (div_le_div_iff₀ hdmax hd).mpr
      exact mul_le_mul_of_nonneg_left hdle hℓ
    _ ≤ _ := parallel_levi_diagonal_lower_bound κ v w hM ht hr hκ hκM hlower

end PowerConvexity
