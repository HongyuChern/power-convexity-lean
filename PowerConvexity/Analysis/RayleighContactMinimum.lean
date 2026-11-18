import PowerConvexity.Analysis.QuadraticPathTangents

/-! # Opposite smooth upper contacts cannot share a minimum on a positive ball

This is the finite-dimensional-free analytic core of Appendix A Cases 2--4.
It differentiates the smooth contacts, never the repeated spectral root.
-/
set_option autoImplicit false
open Set Filter Metric
open scoped Topology
namespace PowerConvexity
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]

theorem no_common_ball_minimum_of_opposite_derivatives
    {f g : P → ℝ} {q h : P} {ε c : ℝ}
    (hε : 0 < ε) (hq : ‖q‖^2 ≤ ε) (hc : c < 0)
    (hf : DifferentiableAt ℝ f q)
    (hdf : HasDerivAt (fun t : ℝ => f (q+t • h)) c 0)
    (hdg : HasDerivAt (fun t : ℝ => g (q+t • h)) (-c) 0)
    (hminf : ∀ r : P, ‖r‖^2 ≤ ε → f q ≤ f r)
    (hming : ∀ r : P, ‖r‖^2 ≤ ε → g q ≤ g r) : False := by
  have hnorm : HasDerivAt (fun t : ℝ => ‖q+t • h‖^2) (2*inner ℝ q h) 0 := by
    simpa using (linearPerturbationPath_hasDerivAt_zero q h).norm_sq
  rcases lt_trichotomy (inner ℝ q h) 0 with hi | hi | hi
  · obtain ⟨δ1,hδ1,hN⟩ := hasDerivAt_negative_right_decrease hnorm (by linarith)
    obtain ⟨δ2,hδ2,hF⟩ := hasDerivAt_negative_right_decrease hdf hc
    let t := min δ1 δ2/2
    have ht : 0 < t := by dsimp [t]; positivity
    have ht1 : t < δ1 := by dsimp [t]; linarith [min_le_left δ1 δ2]
    have ht2 : t < δ2 := by dsimp [t]; linarith [min_le_right δ1 δ2]
    have hNt : ‖q+t • h‖^2 ≤ ε := (by simpa using (hN t ht ht1).le : ‖q+t • h‖^2 ≤ ‖q‖^2).trans hq
    have hFt : f (q+t • h) < f q := by simpa using hF t ht ht2
    exact (not_lt_of_ge (hminf _ hNt)) hFt
  · by_cases hq0 : q = 0
    · have hN0 : ‖q+(0:ℝ) • h‖^2 < ε := by simpa [hq0] using hε
      have hNc : ContinuousAt (fun t : ℝ => ‖q+t • h‖^2) 0 := hnorm.continuousAt
      obtain ⟨δ1,hδ1,hN⟩ := Metric.mem_nhds_iff.mp (hNc.eventually (gt_mem_nhds hN0))
      obtain ⟨δ2,hδ2,hF⟩ := hasDerivAt_negative_right_decrease hdf hc
      let t := min δ1 δ2/2
      have ht : 0 < t := by dsimp [t]; positivity
      have ht1 : t < δ1 := by dsimp [t]; linarith [min_le_left δ1 δ2]
      have ht2 : t < δ2 := by dsimp [t]; linarith [min_le_right δ1 δ2]
      have hNt : ‖q+t • h‖^2 ≤ ε := (hN (by
        simpa only [mem_ball,dist_zero_right,Real.norm_eq_abs,abs_of_pos ht] using ht1)).le
      have hFt : f (q+t • h) < f q := by simpa using hF t ht ht2
      exact (not_lt_of_ge (hminf _ hNt)) hFt
    · obtain ⟨γ,δ1,_,hδ1,hN⟩ := exists_curved_perturbation_norm_decrease q h hq0 hi
      have hD := curvedPerturbationPath_comp_hasDerivAt hf hdf γ
      obtain ⟨δ2,hδ2,hF⟩ := hasDerivAt_negative_right_decrease hD hc
      let t := min δ1 δ2/2
      have ht : 0 < t := by dsimp [t]; positivity
      have ht1 : |t| < δ1 := by rw [abs_of_pos ht]; dsimp [t]; linarith [min_le_left δ1 δ2]
      have ht2 : t < δ2 := by dsimp [t]; linarith [min_le_right δ1 δ2]
      have hNt := (hN t ht1 ht.ne').le.trans hq
      have hFt : f (curvedPerturbationPath q h γ t) < f q := by
        simpa [curvedPerturbationPath] using hF t ht ht2
      exact (not_lt_of_ge (hminf _ hNt)) hFt
  · obtain ⟨δ1,hδ1,hN⟩ := hasDerivAt_positive_left_decrease hnorm (by linarith)
    obtain ⟨δ2,hδ2,hG⟩ := hasDerivAt_positive_left_decrease hdg (by linarith)
    let t := -(min δ1 δ2/2)
    have ht : t < 0 := by dsimp [t]; have := lt_min hδ1 hδ2; linarith
    have ht1 : -δ1 < t := by dsimp [t]; linarith [min_le_left δ1 δ2]
    have ht2 : -δ2 < t := by dsimp [t]; linarith [min_le_right δ1 δ2]
    have hNt : ‖q+t • h‖^2 ≤ ε := (by simpa using (hN t ht1 ht).le : ‖q+t • h‖^2 ≤ ‖q‖^2).trans hq
    have hGt : g (q+t • h) < g q := by simpa using hG t ht2 ht
    exact (not_lt_of_ge (hming _ hNt)) hGt

end PowerConvexity
