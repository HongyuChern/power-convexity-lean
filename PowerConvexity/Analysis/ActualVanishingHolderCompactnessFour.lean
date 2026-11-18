import PowerConvexity.Analysis.ActualFlatBoundaryCompactnessFour
import PowerConvexity.Analysis.ActualUniformWeakHolderFour

/-! # Compactness with an actual vanishing additive Holder error -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace PowerConvexity
local notation "E" => DeGiorgi.AmbientSpace (2+2)

theorem actual_compact_uniform_subsequence_of_vanishing_holder_error_four
    {K : Set E} (hK : IsCompact K) (u : ℕ → E → ℝ)
    (hu : ∀ n, ContinuousOn (u n) K) {M C alpha : ℝ} (halpha : 0 < alpha)
    (hub : ∀ n x, x ∈ K → |u n x| ≤ M)
    (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0))
    (hmod : ∀ n x, x ∈ K → ∀ y, y ∈ K →
      |u n x-u n y| ≤ e n+C*‖x-y‖^alpha) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧ ∃ g : E → ℝ,
      ContinuousOn g K ∧ TendstoUniformlyOn (fun n => u (phi n)) g atTop K ∧
      ∀ x ∈ K, |g x| ≤ M := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  apply compact_equicontinuous_sequence_has_uniform_subsequence hK u hu M
    (by simpa only [Real.norm_eq_abs] using hub)
  apply continuous_sequence_equicontinuous_of_tail_modulus
    (fun n (x : K) => u n x) (fun n => (hu n).restrict)
  intro eps heps
  have hsmall : ∀ᶠ n in atTop, e n < eps/2 :=
    (tendsto_order.1 he).2 _ (half_pos heps)
  have hc : ContinuousAt (fun t : ℝ => C*t^alpha) 0 :=
    continuousAt_const.mul (continuousAt_id.rpow_const (Or.inr halpha.le))
  have hlim : Tendsto (fun t : ℝ => C*t^alpha) (𝓝 0) (𝓝 0) := by
    simpa only [Real.zero_rpow halpha.ne',mul_zero] using hc.tendsto
  obtain ⟨delta,hd,hball⟩ := Metric.mem_nhds_iff.mp
    ((tendsto_order.1 hlim).2 (eps/2) (half_pos heps))
  refine ⟨delta,hd,?_⟩
  filter_upwards [hsmall] with n hn
  intro x y hxy
  have hdist : dist (dist x y) (0 : ℝ) < delta := by simpa only [Real.dist_eq,sub_zero,abs_of_nonneg dist_nonneg] using hxy
  have hh := hball (show dist x y ∈ ball (0 : ℝ) delta from hdist)
  have hm := hmod n x x.property y y.property
  simp only [Subtype.dist_eq,dist_eq_norm,Set.mem_setOf_eq] at hh
  change |u n x-u n y| < eps
  linarith

end PowerConvexity
