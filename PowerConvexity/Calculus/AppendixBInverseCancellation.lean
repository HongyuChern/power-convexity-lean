import PowerConvexity.Calculus.ScalarQuotientCalculus

/-! # The literal B10-1 term and the inverse-route cancellation

The inverse route is used only on the nonsingular locus. The general extremal
jet theorem elsewhere does not require invertibility of the original matrix.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ContDiff
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem paper_B10_1_actual_inverse_term {f : E → ℂ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hx : f x ≠ 0) (a b c d : E) :
    2 / ((f x)⁻¹)^3 * dz a b (fun y => (f y)⁻¹) x * dz c d (fun y => (f y)⁻¹) x =
      (2/f x) * dz a b f x * dz c d f x := by
  rw [dz_inv_at hf hx, dz_inv_at hf hx]
  field_simp <;> ring

theorem actual_inverse_mixed_cancellation {f : E → ℂ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hx : f x ≠ 0) (a b c d : E) :
    -(f x)^2 * dz c d (dz a b (fun y => (f y)⁻¹)) x +
      (2/f x) * dz a b f x * dz c d f x = dz c d (dz a b f) x := by
  rw [dz_mixed_inv_at hf hx]
  field_simp <;> ring

/-- An actual downstream use of B10-1 in the scalar inverse second-jet rule. -/
theorem paper_B9_B10_actual_cancellation {f : E → ℂ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hx : f x ≠ 0) (a b c d : E) :
    -(f x)^2 * dz c d (dz a b (fun y => (f y)⁻¹)) x +
      2 / ((f x)⁻¹)^3 * dz a b (fun y => (f y)⁻¹) x * dz c d (fun y => (f y)⁻¹) x =
        dz c d (dz a b f) x := by
  rw [paper_B10_1_actual_inverse_term (hf.differentiableAt (by norm_num)) hx]
  exact actual_inverse_mixed_cancellation hf hx a b c d

theorem inverse_spectral_gap_coefficient (s t : ℂ) (hs : s ≠ 0) (ht : t ≠ 0) (hst : s ≠ t) :
    1/t + (1/(s^2*t^2))/(1/s-1/t)*s^2 = 1/(t-s) := by
  have hst' : t-s ≠ 0 := sub_ne_zero.mpr (Ne.symm hst)
  field_simp <;> ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem inverse_spectral_mixed_sum_cancellation (k : ι → ℂ) (i : ι)
    (hk : ∀ j, k j ≠ 0) (hgap : ∀ j, j ≠ i → k i ≠ k j)
    (Z : ℂ) (X Y : Matrix ι ι ℂ) :
    Z - ∑ j ∈ Finset.univ.erase i,
      (X i j*Y j i+Y i j*X j i) *
        (1/k j + (1/((k i)^2*(k j)^2))/(1/k i-1/k j)*(k i)^2) =
    Z + ∑ j ∈ Finset.univ.erase i,
      (X i j*Y j i+Y i j*X j i)/(k i-k j) := by
  have he (j : ι) (hj : j ∈ Finset.univ.erase i) :=
    inverse_spectral_gap_coefficient (k i) (k j) (hk i) (hk j) (hgap j (Finset.ne_of_mem_erase hj))
  simp_rw [Finset.sum_congr rfl (fun j hj => congrArg (fun z => (X i j*Y j i+Y i j*X j i)*z) (he j hj))]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simp only [mul_one_div, neg_div, neg_div_neg_eq, neg_sub]
  rw [← div_neg, neg_sub]

end PowerConvexity
