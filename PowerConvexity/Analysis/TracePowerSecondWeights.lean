import PowerConvexity.Analysis.TracePowerNormalization

/-! # The dominant-pair cancellation and all second trace-power weights

The index is p=n+2.  The potentially growing dominant term is cancelled
before taking a limit; no uniform derivative limit is assumed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
open Filter
namespace PowerConvexity
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def traceRootWeight (r : ι → ℝ) (n : ℕ) : ℝ :=
  normalizedTracePower r (n+2) ^ (((n:ℝ)+1)/((n:ℝ)+2))

noncomputable def traceRootSecondWeight (r : ι → ℝ) (n : ℕ) : ℝ :=
  normalizedTracePower r (n+2) * traceRootWeight r n

theorem traceRootWeight_pos (r : ι → ℝ) (i : ι) (hi : r i = 1)
    (h0 : ∀ j, 0 ≤ r j) (n : ℕ) : 0 < traceRootWeight r n :=
  Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one (normalizedTracePower_ge_one r i hi h0 _)) _

theorem traceRootWeight_tendsto (r : ι → ℝ) (i : ι) (hi : r i = 1)
    (h0 : ∀ j, 0 ≤ r j) (hgap : ∀ j, j ≠ i → r j < 1) :
    Tendsto (traceRootWeight r) atTop (𝓝 1) := by
  change Tendsto (fun n : ℕ => normalizedTracePower r (n+2) ^ (((n:ℝ)+1)/((n:ℝ)+2))) _ _
  convert (tendsto_add_atTop_iff_nat 1).2 (normalizedTracePower_weight_tendsto r i hi h0 hgap) using 1
  congr 1
  ext n
  congr 1 <;> push_cast <;> ring

theorem traceRootSecondWeight_tendsto (r : ι → ℝ) (i : ι) (hi : r i = 1)
    (h0 : ∀ j, 0 ≤ r j) (hgap : ∀ j, j ≠ i → r j < 1) :
    Tendsto (traceRootSecondWeight r) atTop (𝓝 1) := by
  have hS : Tendsto (fun n : ℕ => normalizedTracePower r (n+2)) atTop (𝓝 1) := by
    simpa [add_assoc] using
      (tendsto_add_atTop_iff_nat 1).2 (normalizedTracePower_tendsto r i hi h0 hgap)
  change Tendsto (fun n : ℕ => normalizedTracePower r (n+2) * traceRootWeight r n) _ _
  convert hS.mul (traceRootWeight_tendsto r i hi h0 hgap) using 1 <;> first | rfl | simp

theorem divided_power_sum_right_one_tendsto {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    Tendsto (fun n : ℕ => ∑ j ∈ Finset.range (n+1), a^j * 1^(n-j))
      atTop (𝓝 (1/(1-a))) := by
  have he (n : ℕ) : (∑ j ∈ Finset.range (n+1), a^j * (1:ℝ)^(n-j)) =
      (a^(n+1)-1)/(a-1) := by simpa using geom₂_sum (ne_of_lt ha1) (n+1)
  simp_rw [he, pow_succ]
  convert (((tendsto_pow_atTop_nhds_zero_of_lt_one ha0 ha1).mul_const a).sub
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1))).div_const (a-1) using 1
  simp only [zero_mul, zero_sub]
  congr 1
  rw [div_eq_div_iff (by linarith : 1-a ≠ 0) (by linarith : a-1 ≠ 0)]
  ring

/-- Both roots may coincide away from the dominant simple root. -/
theorem traceRoot_offdiag_convolution_tendsto (r : ι → ℝ) (i : ι) (hi : r i = 1)
    (h0 : ∀ j, 0 ≤ r j) (hgap : ∀ j, j ≠ i → r j < 1)
    (l m : ι) (hpair : l ≠ i ∨ m ≠ i) :
    Tendsto (fun n : ℕ => (∑ j ∈ Finset.range (n+1), r l^j*r m^(n-j)) / traceRootWeight r n)
      atTop (𝓝 (if l=i then 1/(1-r m) else if m=i then 1/(1-r l) else 0)) := by
  have hW := traceRootWeight_tendsto r i hi h0 hgap
  by_cases hl : l=i
  · subst l
    have hm : m ≠ i := hpair.resolve_left (not_not_intro rfl)
    convert (divided_power_sum_one_tendsto (h0 m) (hgap m hm)).div hW one_ne_zero using 1
    · ext n; simp [hi]
    · simp [hm]
  · by_cases hm : m=i
    · subst m
      convert (divided_power_sum_right_one_tendsto (h0 l) (hgap l hl)).div hW one_ne_zero using 1
      · ext n; simp [hi]
      · simp [hl]
    · convert (divided_power_sum_tendsto_zero (h0 l) (hgap l hl) (h0 m) (hgap m hm)).div hW one_ne_zero using 1 <;> first | rfl | simp [hl, hm]

theorem traceRoot_rank_offdiag_tendsto (r : ι → ℝ) (i : ι) (hi : r i = 1)
    (h0 : ∀ j, 0 ≤ r j) (hgap : ∀ j, j ≠ i → r j < 1)
    (l m : ι) (hpair : l ≠ i ∨ m ≠ i) :
    Tendsto (fun n : ℕ => ((n:ℝ)+1)*r l^(n+1)*r m^(n+1) / traceRootSecondWeight r n)
      atTop (𝓝 0) := by
  have hp (j : ι) : Tendsto (fun n : ℕ => r j^(n+1)) atTop (𝓝 (if j=i then 1 else 0)) := by
    by_cases hj : j=i
    · subst j; simpa [hi] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1))
    · simpa [hj, pow_succ] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one (h0 j) (hgap j hj)).mul_const (r j)
  have hn (j : ι) (hj : j ≠ i) :
      Tendsto (fun n : ℕ => ((n:ℝ)+1)*r j^(n+1)) atTop (𝓝 0) := by
    simpa [Nat.cast_add] using (tendsto_add_atTop_iff_nat 1).2
      (tendsto_self_mul_const_pow_of_lt_one (h0 j) (hgap j hj))
  have hnum : Tendsto (fun n : ℕ => ((n:ℝ)+1)*r l^(n+1)*r m^(n+1)) atTop (𝓝 0) := by
    rcases hpair with hl | hm
    · simpa using (hn l hl).mul (hp m)
    · convert (hn m hm).mul (hp l) using 1 <;> first | simp | (ext n; ring)
  convert hnum.div (traceRootSecondWeight_tendsto r i hi h0 hgap) one_ne_zero using 1 <;> first | rfl | simp

/-- The two O(p) terms cancel, leaving p times an exponentially small tail. -/
theorem traceRoot_dominant_cancellation_tendsto (r : ι → ℝ) (i : ι) (hi : r i = 1)
    (h0 : ∀ j, 0 ≤ r j) (hgap : ∀ j, j ≠ i → r j < 1) :
    Tendsto (fun n : ℕ => ((n:ℝ)+1)/traceRootWeight r n -
      ((n:ℝ)+1)/traceRootSecondWeight r n) atTop (𝓝 0) := by
  have he (n : ℕ) : ((n:ℝ)+1)/traceRootWeight r n - ((n:ℝ)+1)/traceRootSecondWeight r n =
      (((n:ℝ)+1)*(normalizedTracePower r (n+2)-1))/traceRootSecondWeight r n := by
    have hS : normalizedTracePower r (n+2) ≠ 0 :=
      ne_of_gt (lt_of_lt_of_le zero_lt_one (normalizedTracePower_ge_one r i hi h0 _))
    have hW : traceRootWeight r n ≠ 0 := ne_of_gt (traceRootWeight_pos r i hi h0 n)
    unfold traceRootSecondWeight
    field_simp <;> ring
  have ht : Tendsto (fun n : ℕ => ((n:ℝ)+1)*(normalizedTracePower r (n+2)-1)) atTop (𝓝 0) := by
    simpa [Nat.cast_add, add_assoc] using (tendsto_add_atTop_iff_nat 1).2
      (normalizedTracePower_weighted_tail_tendsto r i hi h0 hgap)
  simp_rw [he]
  convert ht.div (traceRootSecondWeight_tendsto r i hi h0 hgap) one_ne_zero using 1 <;> first | rfl | simp

end PowerConvexity
