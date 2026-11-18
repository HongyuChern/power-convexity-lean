import PowerConvexity.Analysis.TracePowerSecondWeights

/-! # The complete finite-sum second trace-power limit -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
open Filter
namespace PowerConvexity
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def normalizedTraceSecondPair (r : ι → ℝ) (X Y : Matrix ι ι ℂ)
    (l m : ι) (n : ℕ) : ℂ :=
  (((∑ j ∈ Finset.range (n+1), r l^j*r m^(n-j)) / traceRootWeight r n : ℝ):ℂ) * Y l m * X m l -
  ((((n:ℝ)+1)*r l^(n+1)*r m^(n+1) / traceRootSecondWeight r n : ℝ):ℂ) * X l l * Y m m

noncomputable def traceSecondPairLimit (r : ι → ℝ) (i : ι) (X Y : Matrix ι ι ℂ) (l m : ι) : ℂ :=
  if l=i then (if m=i then 0 else Y i m*X m i/((1-r m:ℝ):ℂ))
  else (if m=i then Y l i*X i l/((1-r l:ℝ):ℂ) else 0)

theorem normalizedTraceSecondPair_tendsto (r : ι → ℝ) (i : ι) (hi : r i = 1)
    (h0 : ∀ j, 0 ≤ r j) (hgap : ∀ j, j ≠ i → r j < 1)
    (X Y : Matrix ι ι ℂ) (l m : ι) :
    Tendsto (normalizedTraceSecondPair r X Y l m) atTop (𝓝 (traceSecondPairLimit r i X Y l m)) := by
  by_cases hl : l=i
  · subst l
    by_cases hm : m=i
    · subst m
      have he (n : ℕ) : normalizedTraceSecondPair r X Y i i n =
          ((((n:ℝ)+1)/traceRootWeight r n-((n:ℝ)+1)/traceRootSecondWeight r n : ℝ):ℂ) * (Y i i*X i i) := by
        simp only [normalizedTraceSecondPair, hi, one_pow, mul_one, Finset.sum_const,
          Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one, mul_one]
        push_cast
        ring
      change Tendsto (fun n => normalizedTraceSecondPair r X Y i i n) _ _
      simp_rw [he]
      convert (Complex.continuous_ofReal.continuousAt.tendsto.comp
        (traceRoot_dominant_cancellation_tendsto r i hi h0 hgap)).mul_const (Y i i*X i i) using 1 <;>
        first | rfl | simp [traceSecondPairLimit]
    · have hC := (Complex.continuous_ofReal.continuousAt.tendsto.comp
        (traceRoot_offdiag_convolution_tendsto r i hi h0 hgap i m (Or.inr hm))).mul_const (Y i m) |>.mul_const (X m i)
      have hR := (Complex.continuous_ofReal.continuousAt.tendsto.comp
        (traceRoot_rank_offdiag_tendsto r i hi h0 hgap i m (Or.inr hm))).mul_const (X i i) |>.mul_const (Y m m)
      convert hC.sub hR using 1
      · rfl
      · simp [traceSecondPairLimit, hm, Complex.ofReal_div, div_eq_mul_inv]
        ring
  · have hp : l ≠ i ∨ m ≠ i := Or.inl hl
    have hC := (Complex.continuous_ofReal.continuousAt.tendsto.comp
      (traceRoot_offdiag_convolution_tendsto r i hi h0 hgap l m hp)).mul_const (Y l m) |>.mul_const (X m l)
    have hR := (Complex.continuous_ofReal.continuousAt.tendsto.comp
      (traceRoot_rank_offdiag_tendsto r i hi h0 hgap l m hp)).mul_const (X l l) |>.mul_const (Y m m)
    convert hC.sub hR using 1
    · rfl
    · by_cases hm : m=i
      · subst m
        simp [traceSecondPairLimit, hl, Complex.ofReal_div, div_eq_mul_inv]
        ring
      · simp [traceSecondPairLimit, hl, hm]

theorem traceSecondPairLimit_sum (r : ι → ℝ) (i : ι) (X Y : Matrix ι ι ℂ) :
    (∑ l, ∑ m, traceSecondPairLimit r i X Y l m) =
      ∑ j ∈ Finset.univ.erase i, (Y i j*X j i + X i j*Y j i)/((1-r j:ℝ):ℂ) := by
  have hrow (l : ι) (hl : l ≠ i) :
      (∑ m, traceSecondPairLimit r i X Y l m) = Y l i*X i l/((1-r l:ℝ):ℂ) := by
    simp [traceSecondPairLimit, hl]
  rw [← Finset.sum_erase_add Finset.univ (fun l => ∑ m, traceSecondPairLimit r i X Y l m) (Finset.mem_univ i)]
  rw [← Finset.sum_erase_add Finset.univ (fun m => traceSecondPairLimit r i X Y i m) (Finset.mem_univ i)]
  have hdiag : traceSecondPairLimit r i X Y i i = 0 := by simp [traceSecondPairLimit]
  rw [hdiag, add_zero, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [hrow j (Finset.ne_of_mem_erase hj)]
  simp [traceSecondPairLimit, Finset.ne_of_mem_erase hj] <;> ring

theorem normalizedTraceSecondContraction_tendsto (r : ι → ℝ) (i : ι) (hi : r i = 1)
    (h0 : ∀ j, 0 ≤ r j) (hgap : ∀ j, j ≠ i → r j < 1) (X Y : Matrix ι ι ℂ) :
    Tendsto (fun n : ℕ => ∑ l, ∑ m, normalizedTraceSecondPair r X Y l m n) atTop
      (𝓝 (∑ j ∈ Finset.univ.erase i, (Y i j*X j i + X i j*Y j i)/((1-r j:ℝ):ℂ))) := by
  rw [← traceSecondPairLimit_sum]
  exact tendsto_finsetSum Finset.univ (fun l _ => tendsto_finsetSum Finset.univ
    (fun m _ => normalizedTraceSecondPair_tendsto r i hi h0 hgap X Y l m))

end PowerConvexity
