import PowerConvexity.Analysis.TracePowerUniformWeights

/-! # Uniform coefficient bounds, including repeated off-top eigenvalues -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped BigOperators Topology
namespace PowerConvexity
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem divided_power_one_error_le {a q W T : ℝ}
    (ha : 0 ≤ a) (haq : a ≤ q) (hq : q < 1) (hW : 1 ≤ W)
    (hT : |1/W-1| ≤ T) (n : ℕ) :
    |(∑ j ∈ Finset.range (n+1), (1 : ℝ)^j*a^(n-j))/W - 1/(1-a)| ≤
      (T+q^(n+1))/(1-q) := by
  have hq0 : 0 ≤ q := ha.trans haq
  have ha1 : a < 1 := haq.trans_lt hq
  have hWp : 0 < W := lt_of_lt_of_le zero_lt_one hW
  have hda : 0 < 1-a := sub_pos.mpr ha1
  have hdq : 0 < 1-q := sub_pos.mpr hq
  have hT0 : 0 ≤ T := (abs_nonneg _).trans hT
  have he : (∑ j ∈ Finset.range (n+1), (1 : ℝ)^j*a^(n-j))/W - 1/(1-a) =
      ((1/W-1)-a^(n+1)/W)/(1-a) := by
    have hg : (∑ j ∈ Finset.range (n+1), (1 : ℝ)^j*a^(n-j)) =
        (1-a^(n+1))/(1-a) := by simpa using geom₂_sum (ne_of_gt ha1) (n+1)
    rw [hg]
    field_simp
    <;> ring
  rw [he, abs_div, abs_of_pos hda]
  calc
    _ ≤ (|1/W-1|+|a^(n+1)/W|)/(1-a) :=
      div_le_div_of_nonneg_right (abs_sub _ _) hda.le
    _ ≤ (T+q^(n+1))/(1-a) := by
      apply div_le_div_of_nonneg_right _ hda.le
      apply add_le_add hT
      rw [abs_of_nonneg (div_nonneg (pow_nonneg ha _) hWp.le)]
      exact (div_le_self (pow_nonneg ha _) hW).trans (pow_le_pow_left₀ ha haq _)
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hdq (by linarith)

theorem traceRoot_first_coefficient_error_le (r : ι → ℝ) (i : ι) (hi : r i = 1)
    (h0 : ∀ j, 0 ≤ r j) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hr : ∀ j, j ≠ i → r j ≤ q) (j : ι) (n : ℕ) :
    |r j^(n+1)/traceRootWeight r n - (if j=i then 1 else 0)| ≤
      ((Fintype.card ι : ℝ)+1)*q^n := by
  have hp1 : q^(n+1) ≤ q^n := pow_le_pow_of_le_one hq0 hq1.le (by omega)
  have hp2 : q^(n+2) ≤ q^n := pow_le_pow_of_le_one hq0 hq1.le (by omega)
  by_cases hj : j=i
  · subst j
    simp only [hi, one_pow, if_true]
    exact (traceRootWeight_inv_error_le r i hi h0 hq0 hr n).trans (by
      have := mul_le_mul_of_nonneg_left hp2 (Nat.cast_nonneg (Fintype.card ι) : (0 : ℝ) ≤ _)
      nlinarith [pow_nonneg hq0 n])
  · simp only [if_neg hj, sub_zero]
    rw [abs_of_nonneg (div_nonneg (pow_nonneg (h0 j) _)
      (zero_le_one.trans (traceRootWeight_bounds r i hi h0 n).1))]
    calc
      _ ≤ r j^(n+1) := div_le_self (pow_nonneg (h0 j) _) (traceRootWeight_bounds r i hi h0 n).1
      _ ≤ q^(n+1) := pow_le_pow_left₀ (h0 j) (hr j hj) _
      _ ≤ q^n := hp1
      _ ≤ _ := by nlinarith [Nat.cast_nonneg (Fintype.card ι) (α := ℝ), pow_nonneg hq0 n]

theorem traceRoot_rank_uniform_le (r : ι → ℝ) (i : ι) (hi : r i = 1)
    (h0 : ∀ j, 0 ≤ r j) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hr : ∀ j, j ≠ i → r j ≤ q) (l m : ι) (hp : l ≠ i ∨ m ≠ i) (n : ℕ) :
    |((n : ℝ)+1)*r l^(n+1)*r m^(n+1)/traceRootSecondWeight r n| ≤
      ((n : ℝ)+1)*q^n := by
  have hW := traceRootSecondWeight_ge_one r i hi h0 n
  have hr1 (j : ι) : r j ≤ 1 := by
    by_cases hj : j=i
    · simp only [hj, hi, le_refl]
    · exact (hr j hj).trans hq1.le
  have hpow1 (j : ι) : r j^(n+1) ≤ 1 := pow_le_one₀ (h0 j) (hr1 j)
  have hoff (j : ι) (hj : j ≠ i) : r j^(n+1) ≤ q^n :=
    (pow_le_pow_left₀ (h0 j) (hr j hj) _).trans
      (pow_le_pow_of_le_one hq0 hq1.le (by omega))
  have hnum : 0 ≤ ((n : ℝ)+1)*r l^(n+1)*r m^(n+1) :=
    mul_nonneg (mul_nonneg (by positivity) (pow_nonneg (h0 l) _)) (pow_nonneg (h0 m) _)
  rw [abs_of_nonneg (div_nonneg hnum (zero_le_one.trans hW))]
  calc
    _ ≤ ((n : ℝ)+1)*r l^(n+1)*r m^(n+1) := div_le_self hnum hW
    _ ≤ ((n : ℝ)+1)*q^n := by
      rcases hp with hl | hm
      · have := mul_le_mul (hoff l hl) (hpow1 m) (pow_nonneg (h0 m) _) (pow_nonneg hq0 _)
        nlinarith [mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ (n : ℝ)+1)]
      · have := mul_le_mul (hpow1 l) (hoff m hm) (pow_nonneg (h0 m) _) zero_le_one
        nlinarith [mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ (n : ℝ)+1)]

theorem traceRoot_convolution_uniform_error_le (r : ι → ℝ) (i : ι) (hi : r i = 1)
    (h0 : ∀ j, 0 ≤ r j) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hr : ∀ j, j ≠ i → r j ≤ q) (l m : ι) (hp : l ≠ i ∨ m ≠ i) (n : ℕ) :
    |(∑ j ∈ Finset.range (n+1), r l^j*r m^(n-j))/traceRootWeight r n -
      (if l=i then 1/(1-r m) else if m=i then 1/(1-r l) else 0)| ≤
      (((Fintype.card ι : ℝ)+1)/(1-q)+1)*((n : ℝ)+1)*q^n := by
  have hW := (traceRootWeight_bounds r i hi h0 n).1
  have hq : 0 < 1-q := sub_pos.mpr hq1
  have hp1 : q^(n+1) ≤ q^n := pow_le_pow_of_le_one hq0 hq1.le (by omega)
  have hp2 : q^(n+2) ≤ q^n := pow_le_pow_of_le_one hq0 hq1.le (by omega)
  have hN : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have hreduce : ((Fintype.card ι : ℝ)*q^(n+2)+q^(n+1))/(1-q) ≤
      (((Fintype.card ι : ℝ)+1)/(1-q)+1)*((n : ℝ)+1)*q^n := by
    have h1 : (Fintype.card ι : ℝ)*q^(n+2)+q^(n+1) ≤
        ((Fintype.card ι : ℝ)+1)*q^n := by nlinarith
    have h2 := div_le_div_of_nonneg_right h1 hq.le
    have h3 : 0 ≤ ((Fintype.card ι : ℝ)+1)/(1-q) := by positivity
    have h4 : 0 ≤ q^n := pow_nonneg hq0 _
    have h5 : ((Fintype.card ι : ℝ)+1)*q^n/(1-q) =
        (((Fintype.card ι : ℝ)+1)/(1-q))*q^n := by ring
    rw [h5] at h2
    nlinarith [mul_nonneg h3 h4, mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ _) h4]
  by_cases hl : l=i
  · subst l
    have hm := hp.resolve_left (not_not_intro rfl)
    simp only [hi, if_true]
    exact (divided_power_one_error_le (h0 m) (hr m hm) hq1 hW
      (traceRootWeight_inv_error_le r i hi h0 hq0 hr n) n).trans hreduce
  · by_cases hm : m=i
    · subst m
      simp only [hi, if_neg hl, if_true]
      have he : (∑ j ∈ Finset.range (n+1), r l^j*(1 : ℝ)^(n-j)) =
          ∑ j ∈ Finset.range (n+1), (1 : ℝ)^j*r l^(n-j) := by
        have hla : r l < 1 := (hr l hl).trans_lt hq1
        have hleft : (∑ j ∈ Finset.range (n+1), r l^j*(1 : ℝ)^(n-j)) =
            (r l^(n+1)-1)/(r l-1) := by simpa using geom₂_sum (ne_of_lt hla) (n+1)
        have hright : (∑ j ∈ Finset.range (n+1), (1 : ℝ)^j*r l^(n-j)) =
            (1-r l^(n+1))/(1-r l) := by simpa using geom₂_sum (ne_of_gt hla) (n+1)
        rw [hleft, hright]
        apply (div_eq_div_iff (sub_ne_zero.mpr hla.ne) (sub_ne_zero.mpr hla.ne')).mpr
        ring
      rw [he]
      exact (divided_power_one_error_le (h0 l) (hr l hl) hq1 hW
        (traceRootWeight_inv_error_le r i hi h0 hq0 hr n) n).trans hreduce
    · simp only [if_neg hl, if_neg hm, sub_zero]
      have hs := divided_power_sum_uniform_le (h0 l) (h0 m) (hr l hl) (hr m hm) n
      rw [abs_of_nonneg (div_nonneg hs.1 (by linarith))]
      apply ((div_le_self hs.1 hW).trans hs.2).trans
      have hpos : 0 ≤ ((Fintype.card ι : ℝ)+1)/(1-q) := by positivity
      have hn : 0 ≤ ((n : ℝ)+1)*q^n := by positivity
      nlinarith

end PowerConvexity
