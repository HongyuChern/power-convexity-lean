import PowerConvexity.Analysis.ActualFlatBoundaryQuadraticFieldFour
import PowerConvexity.Analysis.ActualFlatBoundaryFirstDerivativeFour

/-! # Actual first derivatives at every flat boundary centre -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_flat_centered_geometric_remainder_four {R r C : ℝ}
    (hR : 0 < R) (hr : 0 < r) (hr1 : r < 1) (hC : 0 ≤ C) :
    ∃ beta : ℝ, 0 < beta ∧ beta < 1 ∧ ∃ M ≥ 0,
      ∀ (N c : E) (u p : E → ℝ), inner ℝ N c=0 → u c=p c →
      (∀ n : ℕ, ∀ x : E, 0 ≤ inner ℝ N x → ‖x-c‖ ≤ R*r^n →
        |u x-p x| ≤ C*(1/2 : ℝ)^n*(R*r^n)^2) →
      ∀ x : E, 0 ≤ inner ℝ N x → ‖x-c‖ < R/2 →
        |u x-p x| ≤ M*‖x-c‖^2*‖x-c‖^beta := by
  obtain ⟨beta,hbeta,hbeta1,M,hM,hrem⟩ :=
    actual_flat_geometric_remainder_holder_four hR hr hr1 hC
  refine ⟨beta,hbeta,hbeta1,M,hM,?_⟩
  intro N c u p hc hzero herr x hx hnear
  have htrans : ∀ n : ℕ, ∀ z ∈ actualFlatClosedUpperBallFour N (R*r^n),
      |u (c+z)-p (c+z)| ≤ C*(1/2 : ℝ)^n*(R*r^n)^2 := by
    intro n z hz
    apply herr n (c+z)
    · simpa only [inner_add_right,hc,zero_add] using (show 0 ≤ inner ℝ N z from hz.2)
    · simpa only [add_sub_cancel_left,mem_closedBall,dist_zero_right] using hz.1
  have hxsub : 0 ≤ inner ℝ N (x-c) := by simpa only [inner_sub_right,hc,sub_zero] using hx
  simpa only [add_sub_cancel] using hrem N (fun z => u (c+z)) (fun z => p (c+z))
    (by simpa only [add_zero] using hzero) htrans (x-c) hxsub hnear

theorem actual_flat_centered_remainder_hasFDerivWithinAt_four {N c : E} {u p : E → ℝ}
    (hp : IsQuadraticPolynomial p) (hc : inner ℝ N c=0)
    {R M beta : ℝ} (hR : 0 < R) (hM : 0 ≤ M) (hbeta : 0 ≤ beta)
    (herr : ∀ x : E, 0 ≤ inner ℝ N x → ‖x-c‖ < R/2 →
      |u x-p x| ≤ M*‖x-c‖^2*‖x-c‖^beta) :
    HasFDerivWithinAt u (fderiv ℝ p c) {x : E | 0 ≤ inner ℝ N x} c := by
  let S := {x : E | 0 ≤ inner ℝ N x}
  have hO : (fun x => u x-p x) =O[𝓝[S] c] (fun x => ‖x-c‖^2) := by
    apply Asymptotics.IsBigO.of_bound M
    have he : ∀ᶠ x : E in 𝓝 c, ‖x-c‖ < min (R/2) 1 := by
      filter_upwards [Metric.ball_mem_nhds c (lt_min (half_pos hR) zero_lt_one)] with x hx
      simpa only [mem_ball,dist_eq_norm] using hx
    filter_upwards [self_mem_nhdsWithin,he.filter_mono nhdsWithin_le_nhds] with x hx hnorm
    have hxR : ‖x-c‖ < R/2 := hnorm.trans_le (min_le_left _ _)
    have hx1 : ‖x-c‖ ≤ 1 := hnorm.le.trans (min_le_right _ _)
    have hxpow : ‖x-c‖^beta ≤ 1 := Real.rpow_le_one (norm_nonneg _) hx1 hbeta
    have hh := (herr x hx hxR).trans (mul_le_mul_of_nonneg_left hxpow
      (by positivity : 0 ≤ M*‖x-c‖^2))
    simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖x-c‖),mul_one] using hh
  have hz : HasFDerivWithinAt (fun x => u x-p x) (0 : E →L[ℝ] ℝ) S c :=
    hO.hasFDerivWithinAt (by change 0 ≤ inner ℝ N c; rw [hc]) (by norm_num : 1 < (2 : ℕ))
  have hpD : HasFDerivAt p (fderiv ℝ p c) c :=
    ((IsQuadraticPolynomial_contDiff hp 1).differentiable (by norm_num)).differentiableAt.hasFDerivAt
  simpa only [Pi.add_def,sub_add_cancel,zero_add,S] using hz.add hpD.hasFDerivWithinAt

end PowerConvexity
