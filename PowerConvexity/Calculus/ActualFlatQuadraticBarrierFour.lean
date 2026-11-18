import PowerConvexity.Calculus.ActualFlatBoundaryTaylorFour
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

def actualFlatQuadraticBarrierFour (N : E) (c K : ℝ) (x : E) : ℝ :=
  0+(K • innerSL ℝ N) x+((realInnerForm : Bilin)-c • realRankOneForm N) x x

theorem actualFlatQuadraticBarrierFour_formula (N : E) (c K : ℝ) (x : E) :
    actualFlatQuadraticBarrierFour N c K x = ‖x‖^2-c*(inner ℝ N x)^2+K*inner ℝ N x := by
  change 0+K*inner ℝ N x+(inner ℝ x x-c*(inner ℝ N x*inner ℝ N x)) = _
  rw [real_inner_self_eq_norm_sq]
  ring

theorem actualFlatQuadraticBarrierFour_symmetric (N : E) (c : ℝ) :
    ∀ v w : E, ((realInnerForm : Bilin)-c • realRankOneForm N) v w =
      ((realInnerForm : Bilin)-c • realRankOneForm N) w v := by
  intro v w
  change inner ℝ v w-c*(inner ℝ N v*inner ℝ N w) =
    inner ℝ w v-c*(inner ℝ N w*inner ℝ N v)
  rw [real_inner_comm v w]
  ring

theorem actualFlatQuadraticBarrierFour_contDiff (N : E) (c K : ℝ) (k : ℕ∞ω) :
    ContDiff ℝ k (actualFlatQuadraticBarrierFour N c K) :=
  IsQuadraticPolynomial_contDiff
    ⟨0,K • innerSL ℝ N,(realInnerForm : Bilin)-c • realRankOneForm N,
      actualFlatQuadraticBarrierFour_symmetric N c,fun _ => rfl⟩ k

theorem actualFlatQuadraticBarrierFour_hessian (N : E) (c K : ℝ) (x : E) :
    realHessian (actualFlatQuadraticBarrierFour N c K) x =
      (2 : ℝ) • ((realInnerForm : Bilin)-c • realRankOneForm N) :=
  quadratic_coeff_realHessian 0 (K • innerSL ℝ N) ((realInnerForm : Bilin)-c • realRankOneForm N)
    (actualFlatQuadraticBarrierFour_symmetric N c) x

theorem actualFlatQuadraticBarrierFour_spherical_lower {N : E} (hN : ‖N‖=1)
    {c : ℝ} (hc : 0 ≤ c) {x : E} (hx : x ∈ sphere (0 : E) 1)
    (hn : 0 ≤ inner ℝ N x) : 1 ≤ actualFlatQuadraticBarrierFour N c (c+1) x := by
  have hxnorm : ‖x‖=1 := by simpa only [mem_sphere,dist_zero_right] using hx
  have hbound : inner ℝ N x ≤ 1 := by
    simpa only [hN,hxnorm,mul_one] using real_inner_le_norm N x
  rw [actualFlatQuadraticBarrierFour_formula,hxnorm,one_pow]
  nlinarith [mul_nonneg hc (mul_nonneg hn (sub_nonneg.mpr hbound))]

theorem actualFlatQuadraticBarrierFour_flat_nonneg (N : E) (c K : ℝ) {x : E}
    (hx : inner ℝ N x=0) : 0 ≤ actualFlatQuadraticBarrierFour N c K x := by
  rw [actualFlatQuadraticBarrierFour_formula,hx]
  nlinarith [sq_nonneg ‖x‖]

theorem actualFlatQuadraticBarrierFour_normal_upper {N : E} (hN : ‖N‖=1)
    {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) (hd1 : d ≤ 1) :
    actualFlatQuadraticBarrierFour N c (c+1) (d • N) ≤ (c+2)*d := by
  rw [actualFlatQuadraticBarrierFour_formula]
  simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg hd,hN,mul_one,
    inner_smul_right,real_inner_self_eq_norm_sq,one_pow,mul_one]
  nlinarith [mul_nonneg hc (sq_nonneg d),mul_nonneg hd (sub_nonneg.mpr hd1)]

theorem actual_flat_elliptic_normal_boundary_bound_four
    {N : E} (hN : ‖N‖=1) {lam T F : ℝ} (hlam : 0 < lam) (hT : 0 ≤ T) (hF : 0 ≤ F)
    (L : E → Bilin →ₗ[ℝ] ℝ)
    (hL : ∀ x ∈ actualFlatUpperBallFour N 1, HessianPositive (L x))
    (htrace : ∀ x ∈ actualFlatUpperBallFour N 1, L x realInnerForm ≤ T)
    (hnormal : ∀ x ∈ actualFlatUpperBallFour N 1, lam ≤ L x (realRankOneForm N))
    {u : E → ℝ} (huC : ContinuousOn u (actualFlatClosedUpperBallFour N 1))
    (hu2 : ContDiffOn ℝ 2 u (actualFlatUpperBallFour N 1))
    (hLu : ∀ x ∈ actualFlatUpperBallFour N 1, |L x (realHessian u x)| ≤ F)
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
      L x (realHessian P x) < -F := by
    rw [show P=actualFlatQuadraticBarrierFour N c (c+1) from rfl,
      actualFlatQuadraticBarrierFour_hessian,map_smul,map_sub,map_smul,smul_eq_mul,smul_eq_mul]
    have hn := mul_le_mul_of_nonneg_left (hnormal x hx) hc
    linarith [htrace x hx]
  have hU := actualFlatUpperBallFour_isOpen N 1
  have hcl := actualFlatUpperBallFour_closure_subset N 1
  have hK : IsCompact (closure (actualFlatUpperBallFour N 1)) :=
    (isCompact_closedBall (0 : E) 1).of_isClosed_subset isClosed_closure (fun x hx => (hcl hx).1)
  have hupper (v : E → ℝ) (hvC : ContinuousOn v (actualFlatClosedUpperBallFour N 1))
      (hv2 : ContDiffOn ℝ 2 v (actualFlatUpperBallFour N 1))
      (hvL : ∀ x ∈ actualFlatUpperBallFour N 1, -F ≤ L x (realHessian v x))
      (hv0 : ∀ x ∈ closedBall (0 : E) 1, inner ℝ N x=0 → v x=0)
      (hvb : ∀ x ∈ actualFlatClosedUpperBallFour N 1, v x ≤ 1) :
      ∀ x ∈ actualFlatClosedUpperBallFour N 1, v x ≤ P x := by
    have hb (x : E) (hx : x ∈ frontier (actualFlatUpperBallFour N 1)) : v x-P x ≤ 0 := by
      obtain ⟨hxC,hxS|hx0⟩ := actualFlatUpperBallFour_frontier_subset N 1 hx
      · exact sub_nonpos.mpr ((hvb x hxC).trans (actualFlatQuadraticBarrierFour_spherical_lower hN hc hxS hxC.2))
      · rw [hv0 x hxC.1 hx0,zero_sub]
        exact neg_nonpos.mpr (actualFlatQuadraticBarrierFour_flat_nonneg N c (c+1) hx0)
    have hneg := negative_of_positive_contraction_nonpositive_boundary hU hK
      ((hvC.mono hcl).sub hPC.continuous.continuousOn) (hv2.sub hPC.contDiffOn) hb L hL (by
        intro x hx
        change 0 < L x (realHessian (fun y => v y-P y) x)
        rw [realHessian_sub_at (hv2.contDiffAt (hU.mem_nhds hx)) hPC.contDiffAt,map_sub]
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
      rw [realHessian_neg,map_neg]
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
