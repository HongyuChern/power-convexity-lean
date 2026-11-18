import PowerConvexity.Calculus.ActualFlatDriftBarrierDerivativeFour
import PowerConvexity.Calculus.QuadraticTaylor
import PowerConvexity.Analysis.MatrixHessianContraction
import PowerConvexity.Analysis.NonpositiveBoundaryMaximum

/-! # Explicit elliptic barriers at the flat boundary of an actual half ball
The barrier controls every real elliptic positive Hessian contraction with
specified trace and normal lower bounds. No boundary derivative is assumed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
local notation "E" => DeGiorgi.AmbientSpace (2+2)
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_flat_drift_normal_boundary_bound_four
    {N : E} (hN : ‖N‖=1) {lam T F : ℝ} (hlam : 0 < lam) (hT : 0 ≤ T) (hF : 0 ≤ F)
    (L : E → Bilin →ₗ[ℝ] ℝ)
    (hL : ∀ x ∈ actualFlatUpperBallFour N 1, HessianPositive (L x))
    (htrace : ∀ x ∈ actualFlatUpperBallFour N 1, L x realInnerForm ≤ T)
    (hnormal : ∀ x ∈ actualFlatUpperBallFour N 1, lam ≤ L x (realRankOneForm N))
    (b : E → E)
    (hb : ∀ x ∈ actualFlatUpperBallFour N 1,
      (3*((T+F+1)/lam)+3)*‖b x‖ ≤ 1)
    {u : E → ℝ} (huC : ContinuousOn u (actualFlatClosedUpperBallFour N 1))
    (hu2 : ContDiffOn ℝ 2 u (actualFlatUpperBallFour N 1))
    (hLu : ∀ x ∈ actualFlatUpperBallFour N 1, |L x (realHessian u x)+fderiv ℝ u x (b x)| ≤ F)
    (hu0 : ∀ x ∈ closedBall (0 : E) 1, inner ℝ N x=0 → u x=0)
    (hub : ∀ x ∈ actualFlatClosedUpperBallFour N 1, |u x| ≤ 1) :
    ∀ d ∈ Icc (0 : ℝ) 1,
      |u (d • N)| ≤ ((T+F+1)/lam+2)*d := by
  let c := (T+F+1)/lam
  have hc : 0 ≤ c := div_nonneg (by positivity) hlam.le
  have hceq : c*lam=T+F+1 := div_mul_cancel₀ _ hlam.ne'
  let P := actualFlatQuadraticBarrierFour N c (c+1)
  have hPC := actualFlatQuadraticBarrierFour_contDiff N c (c+1) 2
  have hPstrong (x : E) (hx : x ∈ actualFlatUpperBallFour N 1) :
      L x (realHessian P x)+fderiv ℝ P x (b x) < -F := by
    have hLH : L x (realHessian P x) ≤ -2*F-2 := by
      rw [show P=actualFlatQuadraticBarrierFour N c (c+1) from rfl,
        actualFlatQuadraticBarrierFour_hessian,map_smul,map_sub,map_smul,smul_eq_mul,smul_eq_mul]
      have hn := mul_le_mul_of_nonneg_left (hnormal x hx) hc
      linarith [htrace x hx]
    have hgrad : fderiv ℝ P x (b x) ≤ 1 := by
      have hxn : ‖x‖ ≤ 1 := (show ‖x‖ < 1 from by simpa only [mem_ball,dist_zero_right] using hx.1).le
      exact (le_abs_self _).trans ((actual_flat_quadratic_barrier_derivative_bound_four hN hc hxn (b x)).trans (hb x hx))
    linarith
  have hU := actualFlatUpperBallFour_isOpen N 1
  have hcl := actualFlatUpperBallFour_closure_subset N 1
  have hK : IsCompact (closure (actualFlatUpperBallFour N 1)) :=
    (isCompact_closedBall (0 : E) 1).of_isClosed_subset isClosed_closure (fun x hx => (hcl hx).1)
  have hupper (v : E → ℝ) (hvC : ContinuousOn v (actualFlatClosedUpperBallFour N 1))
      (hv2 : ContDiffOn ℝ 2 v (actualFlatUpperBallFour N 1))
      (hvL : ∀ x ∈ actualFlatUpperBallFour N 1, -F ≤ L x (realHessian v x)+fderiv ℝ v x (b x))
      (hv0 : ∀ x ∈ closedBall (0 : E) 1, inner ℝ N x=0 → v x=0)
      (hvb : ∀ x ∈ actualFlatClosedUpperBallFour N 1, v x ≤ 1) :
      ∀ x ∈ actualFlatClosedUpperBallFour N 1, v x ≤ P x := by
    have hb (x : E) (hx : x ∈ frontier (actualFlatUpperBallFour N 1)) : v x-P x ≤ 0 := by
      obtain ⟨hxC,hxS|hx0⟩ := actualFlatUpperBallFour_frontier_subset N 1 hx
      · exact sub_nonpos.mpr ((hvb x hxC).trans (actualFlatQuadraticBarrierFour_spherical_lower hN hc hxS hxC.2))
      · rw [hv0 x hxC.1 hx0,zero_sub]
        exact neg_nonpos.mpr (actualFlatQuadraticBarrierFour_flat_nonneg N c (c+1) hx0)
    have hneg := negative_of_positive_drift_contraction_nonpositive_boundary_four hU hK
      ((hvC.mono hcl).sub hPC.continuous.continuousOn) (hv2.sub hPC.contDiffOn) hb L hL b (by
        intro x hx
        change 0 < L x (realHessian (fun y => v y-P y) x)+fderiv ℝ (fun y => v y-P y) x (b x)
        have hD : fderiv ℝ (fun y => v y-P y) x = fderiv ℝ v x-fderiv ℝ P x := by
          change fderiv ℝ (v-P) x = _
          exact fderiv_sub ((hv2.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num))
            (hPC.contDiffAt.differentiableAt (by norm_num))
        rw [realHessian_sub_at (hv2.contDiffAt (hU.mem_nhds hx)) hPC.contDiffAt,map_sub,hD,_root_.sub_apply]
        linarith [hvL x hx,hPstrong x hx])
    intro x hx
    by_cases hx0 : inner ℝ N x=0
    · rw [hv0 x hx.1 hx0]
      exact actualFlatQuadraticBarrierFour_flat_nonneg N c (c+1) hx0
    by_cases hxS : x ∈ sphere (0 : E) 1
    · exact (hvb x hx).trans (actualFlatQuadraticBarrierFour_spherical_lower hN hc hxS hx.2)
    have hxB : x ∈ ball (0 : E) 1 := mem_ball.mpr
      (lt_of_le_of_ne (mem_closedBall.mp hx.1) (fun he => hxS (mem_sphere.mpr he)))
    exact (sub_neg.mp (hneg x ⟨hxB,lt_of_le_of_ne hx.2 (Ne.symm hx0)⟩)).le
  have huP := hupper u huC hu2 (fun x hx => (abs_le.mp (hLu x hx)).1) hu0
    (fun x hx => (le_abs_self _).trans (hub x hx))
  have hnuP := hupper (fun x => -u x) huC.neg hu2.neg (by
      intro x hx
      have hD : fderiv ℝ (fun y => -u y) x = -fderiv ℝ u x := by
        change fderiv ℝ (-u) x = _
        exact fderiv_neg
      rw [realHessian_neg,map_neg,hD,_root_.neg_apply]
      linarith [(abs_le.mp (hLu x hx)).2])
    (fun x hx hz => by rw [hu0 x hx hz,neg_zero])
    (fun x hx => (neg_le_abs _).trans (hub x hx))
  intro d hd
  have hx : d • N ∈ actualFlatClosedUpperBallFour N 1 := by
    constructor
    · simpa only [mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_nonneg hd.1,hN,mul_one] using hd.2
    · change 0 ≤ inner ℝ N (d • N)
      simpa only [inner_smul_right,real_inner_self_eq_norm_sq,hN,one_pow,mul_one] using hd.1
  have hpx := actualFlatQuadraticBarrierFour_normal_upper hN hc hd.1 hd.2
  exact (abs_le.mpr ⟨by linarith [hnuP _ hx],huP _ hx⟩).trans hpx

end PowerConvexity
