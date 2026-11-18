import PowerConvexity.Analysis.TracePowerUniformCoefficients
import PowerConvexity.Analysis.TracePowerSecondContraction

/-! # A quantitative uniform second-jet contraction estimate

The constants depend on the first jets through M1 squared. The linear
second-jet term is estimated separately, with its necessary M2 dependence.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators Topology
namespace PowerConvexity
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def traceSecondUniformConstant (d : ℕ) (q : ℝ) : ℝ :=
  (d : ℝ)+((d : ℝ)+1)/(1-q)+2

theorem traceSecondUniformConstant_nonneg (d : ℕ) {q : ℝ} (hq : q < 1) :
    0 ≤ traceSecondUniformConstant d q := by
  unfold traceSecondUniformConstant
  have : 0 < 1-q := sub_pos.mpr hq
  positivity

theorem normalizedTraceSecondPair_uniform_error_le
    (r : ι → ℝ) (i : ι) (hi : r i = 1) (h0 : ∀ j, 0 ≤ r j)
    {q M : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 ≤ M)
    (hr : ∀ j, j ≠ i → r j ≤ q) (X Y : Matrix ι ι ℂ)
    (hX : ∀ l m, ‖X l m‖ ≤ M) (hY : ∀ l m, ‖Y l m‖ ≤ M)
    (l m : ι) (n : ℕ) :
    ‖normalizedTraceSecondPair r X Y l m n - traceSecondPairLimit r i X Y l m‖ ≤
      traceSecondUniformConstant (Fintype.card ι) q * M^2 * ((n : ℝ)+1)*q^n := by
  have hq : 0 < 1-q := sub_pos.mpr hq1
  have hN : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have hC := traceSecondUniformConstant_nonneg (Fintype.card ι) hq1
  have hn : 0 ≤ ((n : ℝ)+1)*q^n := by positivity
  have hprod (a b : ℂ) (ha : ‖a‖ ≤ M) (hb : ‖b‖ ≤ M) : ‖a*b‖ ≤ M^2 := by
    rw [norm_mul, pow_two]
    exact mul_le_mul ha hb (norm_nonneg _) hM
  by_cases hp : l = i ∧ m = i
  · rcases hp with ⟨hl,hm⟩
    subst l
    subst m
    have he : normalizedTraceSecondPair r X Y i i n - traceSecondPairLimit r i X Y i i =
        ((((n : ℝ)+1)/traceRootWeight r n-((n : ℝ)+1)/traceRootSecondWeight r n : ℝ) : ℂ) *
          (Y i i*X i i) := by
      simp only [normalizedTraceSecondPair, traceSecondPairLimit, hi, one_pow, mul_one,
        if_true, sub_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      push_cast
      ring
    rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hcan := traceRoot_dominant_cancellation_le r i hi h0 hq0 hr n
    have hp2 : q^(n+2) ≤ q^n := pow_le_pow_of_le_one hq0 hq1.le (by omega)
    calc
      _ ≤ (((n : ℝ)+1)*(Fintype.card ι : ℝ)*q^(n+2))*M^2 :=
        mul_le_mul hcan (hprod _ _ (hY i i) (hX i i)) (norm_nonneg _) (by positivity)
      _ ≤ (((n : ℝ)+1)*(Fintype.card ι : ℝ)*q^n)*M^2 := by gcongr
      _ ≤ _ := by
        have hNC : (Fintype.card ι : ℝ) ≤ traceSecondUniformConstant (Fintype.card ι) q := by
          unfold traceSecondUniformConstant
          have : 0 ≤ ((Fintype.card ι : ℝ)+1)/(1-q) := by positivity
          linarith
        have := mul_le_mul_of_nonneg_right hNC (mul_nonneg (sq_nonneg M) hn)
        nlinarith
  · have hoff : l ≠ i ∨ m ≠ i := not_and_or.mp hp
    let c : ℝ := if l=i then 1/(1-r m) else if m=i then 1/(1-r l) else 0
    have he : normalizedTraceSecondPair r X Y l m n - traceSecondPairLimit r i X Y l m =
        ((((∑ j ∈ Finset.range (n+1), r l^j*r m^(n-j))/traceRootWeight r n-c : ℝ) : ℂ)) *
          (Y l m*X m l) -
        (((((n : ℝ)+1)*r l^(n+1)*r m^(n+1)/traceRootSecondWeight r n : ℝ) : ℂ)) *
          (X l l*Y m m) := by
      by_cases hl : l=i <;> by_cases hm : m=i
      · exact (hp ⟨hl,hm⟩).elim
      all_goals simp only [normalizedTraceSecondPair, traceSecondPairLimit, c, hl, hm,
        if_true, if_false, sub_zero]
      all_goals push_cast
      all_goals ring
    rw [he]
    calc
      _ ≤ ‖((((∑ j ∈ Finset.range (n+1), r l^j*r m^(n-j))/traceRootWeight r n-c : ℝ) : ℂ)) *
          (Y l m*X m l)‖ +
          ‖(((((n : ℝ)+1)*r l^(n+1)*r m^(n+1)/traceRootSecondWeight r n : ℝ) : ℂ)) *
          (X l l*Y m m)‖ := norm_sub_le _ _
      _ ≤ ((((Fintype.card ι : ℝ)+1)/(1-q)+1)*((n : ℝ)+1)*q^n)*M^2 +
          (((n : ℝ)+1)*q^n)*M^2 := by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        apply add_le_add
        · apply mul_le_mul (traceRoot_convolution_uniform_error_le r i hi h0 hq0 hq1 hr l m hoff n)
            (by simpa only [norm_mul] using hprod _ _ (hY l m) (hX m l)) (by positivity) (by positivity)
        · exact mul_le_mul (traceRoot_rank_uniform_le r i hi h0 hq0 hq1 hr l m hoff n)
            (by simpa only [norm_mul] using hprod _ _ (hX l l) (hY m m)) (by positivity) (by positivity)
      _ ≤ _ := by
        unfold traceSecondUniformConstant
        nlinarith [mul_nonneg hN (mul_nonneg (sq_nonneg M) hn)]

theorem normalizedTraceSecondContraction_uniform_error_le
    (r : ι → ℝ) (i : ι) (hi : r i = 1) (h0 : ∀ j, 0 ≤ r j)
    {q M : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 ≤ M)
    (hr : ∀ j, j ≠ i → r j ≤ q) (X Y : Matrix ι ι ℂ)
    (hX : ∀ l m, ‖X l m‖ ≤ M) (hY : ∀ l m, ‖Y l m‖ ≤ M) (n : ℕ) :
    ‖(∑ l, ∑ m, normalizedTraceSecondPair r X Y l m n) -
      (∑ j ∈ Finset.univ.erase i, (Y i j*X j i+X i j*Y j i)/((1-r j : ℝ) : ℂ))‖ ≤
      (Fintype.card ι : ℝ)^2 * traceSecondUniformConstant (Fintype.card ι) q *
        M^2 * ((n : ℝ)+1)*q^n := by
  rw [← traceSecondPairLimit_sum, ← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ l, ‖∑ m, (normalizedTraceSecondPair r X Y l m n-traceSecondPairLimit r i X Y l m)‖ := norm_sum_le _ _
    _ ≤ ∑ l, ∑ m, ‖normalizedTraceSecondPair r X Y l m n-traceSecondPairLimit r i X Y l m‖ :=
      Finset.sum_le_sum (fun l _ => norm_sum_le _ _)
    _ ≤ ∑ _l : ι, ∑ _m : ι,
        traceSecondUniformConstant (Fintype.card ι) q * M^2 * ((n : ℝ)+1)*q^n := by
      apply Finset.sum_le_sum
      intro l _
      apply Finset.sum_le_sum
      intro m _
      exact normalizedTraceSecondPair_uniform_error_le r i hi h0 hq0 hq1 hM hr X Y hX hY l m n
    _ = _ := by simp; ring

theorem normalizedTraceLinearSecond_uniform_error_le
    (r : ι → ℝ) (i : ι) (hi : r i = 1) (h0 : ∀ j, 0 ≤ r j)
    {q M : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 ≤ M)
    (hr : ∀ j, j ≠ i → r j ≤ q) (Z : ι → ℂ) (hZ : ∀ j, ‖Z j‖ ≤ M) (n : ℕ) :
    ‖(∑ j, ((r j^(n+1)/traceRootWeight r n : ℝ) : ℂ)*Z j)-Z i‖ ≤
      (Fintype.card ι : ℝ)*((Fintype.card ι : ℝ)+1)*M*q^n := by
  have he : (∑ j, ((r j^(n+1)/traceRootWeight r n : ℝ) : ℂ)*Z j)-Z i =
      ∑ j, (((r j^(n+1)/traceRootWeight r n-(if j=i then 1 else 0) : ℝ) : ℂ))*Z j := by
    simp only [Complex.ofReal_sub, sub_mul, Finset.sum_sub_distrib]
    simp only [apply_ite Complex.ofReal, Complex.ofReal_one, Complex.ofReal_zero,
      ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [he]
  calc
    _ ≤ ∑ j, ‖(((r j^(n+1)/traceRootWeight r n-(if j=i then 1 else 0) : ℝ) : ℂ))*Z j‖ := norm_sum_le _ _
    _ ≤ ∑ _j : ι, (((Fintype.card ι : ℝ)+1)*q^n)*M := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul (traceRoot_first_coefficient_error_le r i hi h0 hq0 hq1 hr j n)
        (hZ j) (norm_nonneg _) (by positivity)
    _ = _ := by simp; ring

end PowerConvexity
