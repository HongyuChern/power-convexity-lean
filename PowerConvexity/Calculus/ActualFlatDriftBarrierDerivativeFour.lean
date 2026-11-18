import PowerConvexity.Calculus.ActualFlatQuadraticBarrierFour
import PowerConvexity.Analysis.ActualDriftBoundaryMaximumFour

/-! # Explicit derivative control for the boundary barrier with drift -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
local notation "E" => DeGiorgi.AmbientSpace (2+2)
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_flat_quadratic_barrier_derivative_four (N : E) (c K : ℝ) (x v : E) :
    fderiv ℝ (actualFlatQuadraticBarrierFour N c K) x v =
      K*inner ℝ N v+2*(inner ℝ x v-c*inner ℝ N x*inner ℝ N v) := by
  change fderiv ℝ (fun y => 0+(K • innerSL ℝ N) y+
    ((realInnerForm : Bilin)-c • realRankOneForm N) y y) x v = _
  rw [(quadratic_coeff_hasFDerivAt 0 (K • innerSL ℝ N)
    ((realInnerForm : Bilin)-c • realRankOneForm N)
    (actualFlatQuadraticBarrierFour_symmetric N c) x).fderiv]
  change K*inner ℝ N v+2*(inner ℝ x v-c*(inner ℝ N x*inner ℝ N v)) = _
  ring

theorem actual_flat_quadratic_barrier_derivative_bound_four {N : E} (hN : ‖N‖=1)
    {c : ℝ} (hc : 0 ≤ c) {x : E} (hx : ‖x‖ ≤ 1) (v : E) :
    |fderiv ℝ (actualFlatQuadraticBarrierFour N c (c+1)) x v| ≤ (3*c+3)*‖v‖ := by
  have hNv : |inner ℝ N v| ≤ ‖v‖ := by simpa only [hN,one_mul] using abs_real_inner_le_norm N v
  have hNx : |inner ℝ N x| ≤ 1 := by
    have h := abs_real_inner_le_norm N x
    rw [hN,one_mul] at h
    exact h.trans hx
  have hxv : |inner ℝ x v| ≤ ‖v‖ :=
    (abs_real_inner_le_norm x v).trans (by nlinarith [norm_nonneg v])
  have hm : |inner ℝ N x| * |inner ℝ N v| ≤ ‖v‖ := by
    calc
      _ ≤ 1*|inner ℝ N v| := mul_le_mul_of_nonneg_right hNx (abs_nonneg _)
      _ ≤ _ := by simpa only [one_mul] using hNv
  rw [actual_flat_quadratic_barrier_derivative_four]
  calc
    _ ≤ |(c+1)*inner ℝ N v|+|2*(inner ℝ x v-c*inner ℝ N x*inner ℝ N v)| := abs_add_le _ _
    _ = (c+1)*|inner ℝ N v|+2*|inner ℝ x v-c*inner ℝ N x*inner ℝ N v| := by
      rw [abs_mul,abs_mul,abs_of_nonneg (by positivity : 0 ≤ c+1),abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ (c+1)*|inner ℝ N v|+2*(|inner ℝ x v|+c*(|inner ℝ N x| * |inner ℝ N v|)) := by
      gcongr
      have hh := norm_sub_le (inner ℝ x v) (c*inner ℝ N x*inner ℝ N v)
      simpa only [Real.norm_eq_abs,abs_mul,abs_of_nonneg hc,mul_assoc] using hh
    _ ≤ (3*c+3)*‖v‖ := by nlinarith [mul_le_mul_of_nonneg_left hm hc,mul_le_mul_of_nonneg_left hNv (show 0 ≤ c+1 by positivity)]

end PowerConvexity
