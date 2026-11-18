import PowerConvexity.Analysis.ActualQuadraticTwoCenterJetsTwo

/-! # Geometric scale selection at an actual two-centre distance -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology
namespace PowerConvexity

theorem actual_geometric_half_radius_select_two
    {R theta d : ℝ} (hR : 0 < R) (htheta : 0 < theta) (htheta1 : theta < 1)
    (N : ℕ) (hd : 0 < d) (hsmall : d < R*theta^N/2) :
    ∃ k : ℕ, d ≤ R*theta^(N+k)/2 ∧ R*theta^(N+k)/2 < d/theta := by
  have hden : 0 < R*theta^N := mul_pos hR (pow_pos htheta N)
  have hx : 0 < 2*d/(R*theta^N) := div_pos (by positivity) hden
  have hx1 : 2*d/(R*theta^N) ≤ 1 := by
    apply (div_le_iff₀ hden).mpr
    linarith
  obtain ⟨k,hlo,hhi⟩ := exists_nat_pow_near_of_lt_one hx hx1 htheta htheta1
  have hlo' := (lt_div_iff₀ hden).mp hlo
  have hhi' := (div_le_iff₀ hden).mp hhi
  refine ⟨k,?_,?_⟩
  · rw [pow_add]
    nlinarith only [hhi']
  · apply (lt_div_iff₀ htheta).mpr
    rw [pow_add]
    rw [pow_succ] at hlo'
    nlinarith only [hlo']

end PowerConvexity
