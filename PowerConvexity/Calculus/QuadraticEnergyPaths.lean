import PowerConvexity.Calculus.QuadraticClass
import PowerConvexity.Calculus.QuadraticL2Control
import PowerConvexity.Analysis.QuadraticPerturbationPaths

/-! # Appendix A perturbation paths for the actual integral energy -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Metric
open scoped Topology
namespace PowerConvexity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

noncomputable def quadraticL2Pairing (μ : Measure E) (K : Set E) (q h : E → ℝ) : ℝ :=
  ∫ y in K, q y * h y ∂μ

theorem quadraticL2Energy_const_mul (μ : Measure E) (K : Set E) (q : E → ℝ) (r : ℝ) :
    quadraticL2Energy μ K (fun y => r*q y) = r^2*quadraticL2Energy μ K q := by
  unfold quadraticL2Energy
  simp_rw [mul_pow]
  exact integral_const_mul _ _

theorem quadraticL2Energy_linear_combination (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
    {K : Set E} (hK : IsCompact K) {q h : E → ℝ}
    (hq : ContinuousOn q K) (hh : ContinuousOn h K) (s t : ℝ) :
    quadraticL2Energy μ K (fun y => s*q y+t*h y) =
      s^2*quadraticL2Energy μ K q + 2*s*t*quadraticL2Pairing μ K q h +
        t^2*quadraticL2Energy μ K h := by
  have hq2 : IntegrableOn (fun y => (q y)^2) K μ :=
    (hq.pow 2).integrableOn_compact hK
  have hh2 : IntegrableOn (fun y => (h y)^2) K μ :=
    (hh.pow 2).integrableOn_compact hK
  have hqh : IntegrableOn (fun y => q y*h y) K μ :=
    (hq.mul hh).integrableOn_compact hK
  have he : (fun y => (s*q y+t*h y)^2) =
      (fun y => s^2*(q y)^2+(2*s*t)*(q y*h y)+t^2*(h y)^2) := by
    funext y; ring
  unfold quadraticL2Energy quadraticL2Pairing
  rw [he,integral_add
    (f := fun y => s^2*(q y)^2+(2*s*t)*(q y*h y))
    (g := fun y => t^2*(h y)^2)
    ((hq2.const_mul (s^2)).add (hqh.const_mul (2*s*t))) (hh2.const_mul (t^2)),
    integral_add (f := fun y => s^2*(q y)^2) (g := fun y => (2*s*t)*(q y*h y))
      (hq2.const_mul (s^2)) (hqh.const_mul (2*s*t))]
  simp only [integral_const_mul]

/-- Frozen Appendix A Case 3: the actual remainder is quartic. -/
theorem quadraticL2Energy_curved_difference (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
    {K : Set E} (hK : IsCompact K) {q h : E → ℝ}
    (hq : ContinuousOn q K) (hh : ContinuousOn h K) (γ t : ℝ)
    (horth : quadraticL2Pairing μ K q h = 0) :
    quadraticL2Energy μ K (fun y => (1-γ*t^2)*q y+t*h y) - quadraticL2Energy μ K q =
      t^2*(quadraticL2Energy μ K h-2*γ*quadraticL2Energy μ K q+
        γ^2*t^2*quadraticL2Energy μ K q) := by
  rw [quadraticL2Energy_linear_combination μ hK hq hh, horth]
  ring

theorem exists_curved_quadratic_energy_decrease (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
    {K : Set E} (hK : IsCompact K) {q h : E → ℝ}
    (hq : ContinuousOn q K) (hh : ContinuousOn h K)
    (hEq : 0 < quadraticL2Energy μ K q) (horth : quadraticL2Pairing μ K q h = 0) :
    ∃ γ δ : ℝ, 0 < γ ∧ 0 < δ ∧ ∀ t : ℝ, |t| < δ → t ≠ 0 →
      quadraticL2Energy μ K (fun y => (1-γ*t^2)*q y+t*h y) < quadraticL2Energy μ K q := by
  let Q := quadraticL2Energy μ K q
  let H := quadraticL2Energy μ K h
  let γ := (H+1)/Q
  have hH : 0 ≤ H := quadraticL2Energy_nonneg μ K h
  have hγ : 0 < γ := div_pos (by linarith) hEq
  have hγQ : γ*Q = H+1 := div_mul_cancel₀ _ hEq.ne'
  let A : ℝ → ℝ := fun t => H-2*γ*Q+γ^2*t^2*Q
  have hA0 : A 0 < 0 := by dsimp [A]; nlinarith
  have hAc : ContinuousAt A 0 := by dsimp [A]; fun_prop
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (hAc.eventually (gt_mem_nhds hA0))
  refine ⟨γ,δ,hγ,hδ,?_⟩
  intro t ht ht0
  have hAt : A t < 0 := hball (by simpa only [mem_ball,dist_zero_right,Real.norm_eq_abs] using ht)
  have hp : t^2*A t < 0 := mul_neg_of_pos_of_neg (sq_pos_of_ne_zero ht0) hAt
  have he := quadraticL2Energy_curved_difference μ hK hq hh γ t horth
  change _ = t^2*A t at he
  linarith

/-- The radius test needed in Cases 1 and 4 uses the genuine energy and a
strictly positive parameter. -/
theorem exists_positive_scaled_energy_radius (μ : Measure E) (K : Set E)
    (q : E → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| ≤ δ →
      quadraticL2Energy μ K (fun y => t*q y) ≤ ε := by
  let D := quadraticL2Energy μ K q
  have hD : 0 ≤ D := quadraticL2Energy_nonneg μ K q
  let δ := min 1 (ε/(D+1))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε (by linarith))
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδD : δ*(D+1) ≤ ε :=
    (le_div_iff₀ (by linarith : 0 < D+1)).mp (min_le_right _ _)
  refine ⟨δ,hδ,?_⟩
  intro t ht
  rw [quadraticL2Energy_const_mul]
  have hs : t^2 ≤ δ^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg t) ht 2
  have hδs : δ^2 ≤ δ := by nlinarith
  have hm := mul_le_mul_of_nonneg_right (hs.trans hδs) hD
  change t^2*D ≤ ε
  nlinarith

end PowerConvexity
