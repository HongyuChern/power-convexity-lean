import PowerConvexity.Analysis.ActualLocalDriftOscillationFour

/-! # A physical radius controlling the actual source and drift simultaneously -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace PowerConvexity
local notation "E" => DeGiorgi.AmbientSpace (2+2)

theorem actual_local_drift_error_radius_four {U : Set E} (hU : IsOpen U)
    {x : E} (hx : x ∈ U) {B F eps : ℝ} (hB : 0 ≤ B) (hF : 0 ≤ F) (heps : 0 < eps) :
    ∃ r > 0, r ≤ 1 ∧ closedBall x r ⊆ U ∧ r*B ≤ 1/2 ∧ 2*r^2*(F+1) < eps/2 := by
  obtain ⟨R,hR,hRU⟩ := Metric.isOpen_iff.mp hU x hx
  let q := Real.sqrt (eps/(16*(F+1)))
  have hF1 : 0 < F+1 := by linarith
  have hB1 : 0 < B+1 := by linarith
  have hrat : 0 < eps/(16*(F+1)) := div_pos heps (by positivity)
  have hq : 0 < q := Real.sqrt_pos.mpr hrat
  let r := min 1 (min (R/2) (min (1/(4*(B+1))) q))
  have hr : 0 < r := lt_min (by norm_num) (lt_min (half_pos hR)
    (lt_min (div_pos (by norm_num) (by positivity)) hq))
  have hr1 : r ≤ 1 := min_le_left _ _
  have hrR : r ≤ R/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hrB : r ≤ 1/(4*(B+1)) := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrq : r ≤ q := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hball : closedBall x r ⊆ U := (closedBall_subset_ball (by linarith : r < R)).trans hRU
  have hsmall : r*B ≤ 1/2 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 4*(B+1))).mp hrB
    nlinarith
  have hsq : r^2 ≤ eps/(16*(F+1)) := by
    have hh := (sq_le_sq₀ hr.le hq.le).mpr hrq
    simpa only [q,Real.sq_sqrt hrat.le] using hh
  have herr : 2*r^2*(F+1) < eps/2 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 16*(F+1))).mp hsq
    nlinarith
  exact ⟨r,hr,hr1,hball,hsmall,herr⟩

end PowerConvexity
