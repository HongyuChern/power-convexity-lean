import PowerConvexity.Analysis.TracePowerSecondWeights
import Mathlib.Topology.MetricSpace.Bounded

/-! # Uniform spectral weights with a single normalized gap

All constants precede the spectral vector. The largest ratio is one and
every other ratio lies in [0,q], with q < 1. Repeated off-top ratios are
allowed. The estimates retain the polynomial factor in the power index.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators Topology
open Filter
namespace PowerConvexity
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem normalizedTracePower_tail_le (r : ι → ℝ) (i : ι) (hi : r i = 1)
    (h0 : ∀ j, 0 ≤ r j) {q : ℝ} (hq : 0 ≤ q)
    (hr : ∀ j, j ≠ i → r j ≤ q) (p : ℕ) :
    0 ≤ normalizedTracePower r p - 1 ∧
      normalizedTracePower r p - 1 ≤ (Fintype.card ι : ℝ) * q^p := by
  have he : normalizedTracePower r p - 1 = ∑ j ∈ Finset.univ.erase i, r j^p := by
    have hs := Finset.sum_erase_add Finset.univ (fun j => r j^p) (Finset.mem_univ i)
    simp only [hi, one_pow] at hs
    unfold normalizedTracePower
    rw [← hs, add_sub_cancel_right]
  rw [he]
  refine ⟨Finset.sum_nonneg (fun j _ => pow_nonneg (h0 j) p), ?_⟩
  calc
    _ ≤ ∑ _j ∈ Finset.univ.erase i, q^p := by
      apply Finset.sum_le_sum
      intro j hj
      exact pow_le_pow_left₀ (h0 j) (hr j (Finset.ne_of_mem_erase hj)) p
    _ ≤ ∑ _j : ι, q^p := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.erase_subset _ _) (fun _ _ _ => pow_nonneg hq p)
    _ = _ := by simp

theorem traceRootWeight_bounds (r : ι → ℝ) (i : ι) (hi : r i = 1)
    (h0 : ∀ j, 0 ≤ r j) (n : ℕ) :
    1 ≤ traceRootWeight r n ∧ traceRootWeight r n ≤ normalizedTracePower r (n+2) := by
  have hS := normalizedTracePower_ge_one r i hi h0 (n+2)
  have ha0 : 0 ≤ ((n : ℝ)+1)/((n : ℝ)+2) := by positivity
  have ha1 : ((n : ℝ)+1)/((n : ℝ)+2) ≤ 1 :=
    (div_le_one (by positivity)).mpr (by linarith)
  exact ⟨Real.one_le_rpow hS ha0, Real.rpow_le_self_of_one_le hS ha1⟩

theorem traceRootSecondWeight_ge_one (r : ι → ℝ) (i : ι) (hi : r i = 1)
    (h0 : ∀ j, 0 ≤ r j) (n : ℕ) : 1 ≤ traceRootSecondWeight r n := by
  have hS := normalizedTracePower_ge_one r i hi h0 (n+2)
  have hW := (traceRootWeight_bounds r i hi h0 n).1
  change 1 ≤ normalizedTracePower r (n+2) * traceRootWeight r n
  nlinarith [mul_nonneg (sub_nonneg.mpr hS) (sub_nonneg.mpr hW)]

theorem traceRootWeight_inv_error_le (r : ι → ℝ) (i : ι) (hi : r i = 1)
    (h0 : ∀ j, 0 ≤ r j) {q : ℝ} (hq : 0 ≤ q)
    (hr : ∀ j, j ≠ i → r j ≤ q) (n : ℕ) :
    |1 / traceRootWeight r n - 1| ≤ (Fintype.card ι : ℝ) * q^(n+2) := by
  obtain ⟨hW, hWS⟩ := traceRootWeight_bounds r i hi h0 n
  have hWp : 0 < traceRootWeight r n := lt_of_lt_of_le zero_lt_one hW
  have hle : 1 / traceRootWeight r n ≤ 1 := (div_le_one hWp).mpr hW
  rw [abs_of_nonpos (sub_nonpos.mpr hle)]
  have hcalc : -(1 / traceRootWeight r n - 1) =
      (traceRootWeight r n - 1) / traceRootWeight r n := by field_simp; ring
  rw [hcalc]
  calc
    _ ≤ traceRootWeight r n - 1 := div_le_self (sub_nonneg.mpr hW) hW
    _ ≤ normalizedTracePower r (n+2) - 1 := sub_le_sub_right hWS 1
    _ ≤ _ := (normalizedTracePower_tail_le r i hi h0 hq hr _).2

theorem traceRoot_dominant_cancellation_le (r : ι → ℝ) (i : ι) (hi : r i = 1)
    (h0 : ∀ j, 0 ≤ r j) {q : ℝ} (hq : 0 ≤ q)
    (hr : ∀ j, j ≠ i → r j ≤ q) (n : ℕ) :
    |((n : ℝ)+1)/traceRootWeight r n - ((n : ℝ)+1)/traceRootSecondWeight r n| ≤
      ((n : ℝ)+1) * (Fintype.card ι : ℝ) * q^(n+2) := by
  have hS := normalizedTracePower_ge_one r i hi h0 (n+2)
  have hW := (traceRootWeight_bounds r i hi h0 n).1
  have hSW := traceRootSecondWeight_ge_one r i hi h0 n
  have he : ((n : ℝ)+1)/traceRootWeight r n - ((n : ℝ)+1)/traceRootSecondWeight r n =
      (((n : ℝ)+1)*(normalizedTracePower r (n+2)-1))/traceRootSecondWeight r n := by
    have hSn : normalizedTracePower r (n+2) ≠ 0 := ne_of_gt (by linarith)
    have hWn : traceRootWeight r n ≠ 0 := ne_of_gt (by linarith)
    unfold traceRootSecondWeight
    field_simp
    <;> ring
  rw [he, abs_of_nonneg (by positivity)]
  calc
    _ ≤ ((n : ℝ)+1)*(normalizedTracePower r (n+2)-1) :=
      div_le_self (by positivity) hSW
    _ ≤ ((n : ℝ)+1)*((Fintype.card ι : ℝ)*q^(n+2)) :=
      mul_le_mul_of_nonneg_left (normalizedTracePower_tail_le r i hi h0 hq hr _).2 (by positivity)
    _ = _ := by ring

theorem divided_power_sum_uniform_le {a b q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (haq : a ≤ q) (hbq : b ≤ q) (n : ℕ) :
    0 ≤ ∑ j ∈ Finset.range (n+1), a^j*b^(n-j) ∧
      (∑ j ∈ Finset.range (n+1), a^j*b^(n-j)) ≤ ((n : ℝ)+1)*q^n := by
  have hq : 0 ≤ q := ha.trans haq
  refine ⟨Finset.sum_nonneg (fun j _ => mul_nonneg (pow_nonneg ha _) (pow_nonneg hb _)), ?_⟩
  calc
    _ ≤ ∑ j ∈ Finset.range (n+1), q^n := by
      apply Finset.sum_le_sum
      intro j hj
      have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      calc
        _ ≤ q^j*q^(n-j) := mul_le_mul (pow_le_pow_left₀ ha haq _) (pow_le_pow_left₀ hb hbq _)
          (pow_nonneg hb _) (pow_nonneg hq _)
        _ = _ := by rw [← pow_add, Nat.add_sub_of_le hjn]
    _ = _ := by simp

theorem geometric_polynomial_uniform_rate {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Tendsto (fun n : ℕ => ((n : ℝ)+1)*q^n) atTop (𝓝 0) := by
  simpa [add_mul] using (tendsto_self_mul_const_pow_of_lt_one hq0 hq1).add
    (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1)

end PowerConvexity
