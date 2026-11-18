import PowerConvexity.Analysis.CMADeviationLaplacianTwo

/-! # Actual local mean control for the nonnegative upper deficit.
Local C2 data are extended by the proved smooth cutoff construction only
for applying weak Harnack. The result is transferred back pointwise and
under the actual integral on the smaller ball.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology BigOperators ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)

theorem actual_shifted_CMA_upper_deficit_rescaled_mean_two
    {U : Set E} (hU : IsOpen U) {w : E → ℝ} (hw : ContDiffOn ℝ 2 w U)
    (hpsh : ∀ x ∈ U, (1+complexHessian realDirections imagDirections w x).PosSemidef)
    (hdet : ∀ x ∈ U, (1+complexHessian realDirections imagDirections w x).det = 1)
    {x₀ : E} {r R : ℝ} (hr : 0 < r) (hrR : r < R) (hclosed : closedBall x₀ R ⊆ U)
    (b : ℝ) (hupper : ∀ x ∈ ball x₀ r, w x ≤ b)
    {y : E} (hy : y ∈ ball x₀ (r/4)) :
    (∫ z in ball (0 : E) (1/4 : ℝ), b-w (x₀+r • z)) ≤
      weakHarnackMeanConstant (2+2) (by norm_num) 1 * (b-w y) := by
  let A := identityNormalizedEllipticCoeffTwo (ball x₀ r)
  have hneg := actual_shifted_CMA_negative_local_supersolution_two hU hw hpsh hdet hr hrR hclosed
  have hraw : IsSupersolution A.1 (fun x => b-w x) := by
    simpa only [sub_neg_eq_add,neg_add_eq_sub] using hneg.sub_const_ball hr (-b)
  let v := cutoffRepresentative x₀ r R (fun x => b-w x)
  have hv : ContDiff ℝ 2 v := cutoffRepresentative_contDiff hU hr hrR hclosed
    (contDiffOn_const.sub hw)
  have heq : EqOn v (fun x => b-w x) (ball x₀ r) := cutoffRepresentative_eqOn hrR _
  have hvs : IsSupersolution A.1 v := by
    apply DeGiorgi.IsSupersolution.congr_ae (hsuper := hraw)
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact (heq hx).symm
  have hvnon : ∀ x ∈ ball x₀ r, 0 ≤ v x := by
    intro x hx
    rw [heq hx]
    exact sub_nonneg.mpr (hupper x hx)
  have hh := weak_harnack_rescaled_mean_le (by norm_num : 2 < ((2+2 : ℕ) : ℝ))
    hr A hv.continuous hvnon hvs hy
  have hmap (z : E) (hz : z ∈ ball (0 : E) (1/4 : ℝ)) : x₀+r • z ∈ ball x₀ r := by
    have hz1 : z ∈ ball (0 : E) 1 := (ball_subset_ball (by norm_num : (1/4 : ℝ) ≤ 1)) hz
    have he := congrArg (fun s : Set E => z ∈ s)
      (affine_preimage_ball_mul (d := 2+2) (x₀ := x₀) (R := r) (ρ := 1) hr)
    simpa only [mul_one,mem_preimage] using he.mpr hz1
  have hint : (∫ z in ball (0 : E) (1/4 : ℝ), v (x₀+r • z)) =
      ∫ z in ball (0 : E) (1/4 : ℝ), b-w (x₀+r • z) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    exact heq (hmap z hz)
  have hyr : y ∈ ball x₀ r := (ball_subset_ball (by linarith only [hr] : r/4 ≤ r)) hy
  rw [hint,heq hyr] at hh
  exact hh

end PowerConvexity
