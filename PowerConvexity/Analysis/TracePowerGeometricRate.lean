import PowerConvexity.Analysis.TracePowerUniformWeights

/-! # From an absolute spectral gap to an exponential uniform rate -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Topology
open Filter Set
namespace PowerConvexity

theorem spectral_ratio_le_of_gap {a b L γ : ℝ}
    (ha : 0 < a) (hL : a ≤ L) (hγ : 0 < γ) (hgap : γ ≤ a-b) :
    b/a ≤ 1-γ/L := by
  have hLp : 0 < L := ha.trans_le hL
  have h1 : b/a ≤ 1-γ/a := by
    apply (div_le_iff₀ ha).mpr
    have he : (1-γ/a)*a = a-γ := by field_simp <;> ring
    rw [he]
    linarith
  have h2 := div_le_div_of_nonneg_left hγ.le ha hL
  linarith

theorem geometric_polynomial_exponential_envelope {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ n : ℕ, ((n : ℝ)+1)*q^n ≤ C*Real.exp (-c*(n : ℝ)) := by
  let s : ℝ := (q+1)/2
  have hs0 : 0 < s := by dsimp [s]; linarith
  have hs1 : s < 1 := by dsimp [s]; linarith
  have hqs : q < s := by dsimp [s]; linarith
  have ht := geometric_polynomial_uniform_rate (div_nonneg hq0 hs0.le) ((div_lt_one hs0).mpr hqs)
  obtain ⟨C, hC, hb⟩ := (Metric.isBounded_range_of_tendsto _ ht).exists_pos_norm_le
  refine ⟨C, -Real.log s, hC, neg_pos.mpr (Real.log_neg hs0 hs1), ?_⟩
  intro n
  have hn := hb _ (mem_range_self n)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at hn
  have he : (((n : ℝ)+1)*(q/s)^n)*s^n = ((n : ℝ)+1)*q^n := by
    rw [mul_assoc, div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hs0.ne')]
  have hexp : s^n = Real.exp (-(-Real.log s)*(n : ℝ)) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hs0]
    simp
  rw [← he, ← hexp]
  exact mul_le_mul_of_nonneg_right hn (pow_nonneg hs0.le _)

end PowerConvexity
