import PowerConvexity.Analysis.ActualUniformFlatZeroQuotientFour
import PowerConvexity.Analysis.ActualUniformClosureTangentialResponseFour
import Mathlib.Analysis.Calculus.TangentCone.Real

/-! # The quotient slope identifies the actual mixed closure Hessian

The boundary derivative is derived from the power remainder and compared
with the actual derivative of J.derivative(T), composed with the real chart.
The result retains the derivative of the variable tangential field.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Set Filter Metric Matrix MeasureTheory Asymptotics
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_closed_halfball_uniqueDiff_zero_four {N : E} (hN : ‖N‖=1)
    {R : ℝ} (hR : 0 < R) :
    UniqueDiffWithinAt ℝ (actualFlatClosedUpperBallFour N R) (0 : E) := by
  have hconv : Convex ℝ (actualFlatClosedUpperBallFour N R) :=
    (convex_closedBall (0 : E) R).inter (convex_halfSpace_ge (innerSL ℝ N).toLinearMap.isLinear 0)
  have hm : (R/2) • N ∈ actualFlatUpperBallFour N R := by
    constructor
    · simp only [mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (half_pos hR),hN,mul_one]
      linarith
    · change 0 < inner ℝ N ((R/2) • N)
      rw [inner_smul_right,real_inner_self_eq_norm_sq,hN,one_pow,mul_one]
      exact half_pos hR
  have hsub : actualFlatUpperBallFour N R ⊆ actualFlatClosedUpperBallFour N R :=
    fun x hx => ⟨ball_subset_closedBall hx.1,(show 0 < inner ℝ N x from hx.2).le⟩
  have hi : (interior (actualFlatClosedUpperBallFour N R)).Nonempty := by
    refine ⟨(R/2) • N,mem_interior_iff_mem_nhds.mpr ?_⟩
    exact Filter.mem_of_superset ((actualFlatUpperBallFour_isOpen N R).mem_nhds hm) hsub
  apply uniqueDiffWithinAt_convex hconv hi
  apply subset_closure
  exact ⟨mem_closedBall_self hR.le,by simp⟩

theorem actual_quotient_remainder_hasFDerivWithinAt_four {N : E} (hN : ‖N‖=1)
    {u : E → ℝ} {a C alpha R : ℝ} (hC : 0 ≤ C) (ha : 0 < alpha) (hR : 0 < R)
    (herr : ∀ x ∈ actualFlatClosedUpperBallFour N R,
      |u x-a*inner ℝ N x| ≤ C*‖x‖^alpha*inner ℝ N x) :
    HasFDerivWithinAt u (a • innerSL ℝ N) {x : E | 0 ≤ inner ℝ N x} 0 := by
  have hu0 : u 0=0 := by
    have hh := herr 0 ⟨mem_closedBall_self hR.le,by simp⟩
    simp only [inner_zero_right,mul_zero,sub_zero] at hh
    exact abs_eq_zero.mp (le_antisymm hh (abs_nonneg _))
  have hp : Tendsto (fun x : E => C*‖x‖^alpha) (𝓝 (0 : E)) (𝓝 0) := by
    have hn : Tendsto (fun x : E => ‖x‖) (𝓝 (0 : E)) (𝓝 0) := by
      simpa only [norm_zero] using (continuous_norm.tendsto (0 : E))
    simpa only [mul_zero] using (hn.rpow_const_nhds_zero ha).const_mul C
  apply HasFDerivWithinAt.of_isLittleO
  apply Asymptotics.IsLittleO.of_bound
  intro eps heps
  have hs : ∀ᶠ x : E in 𝓝 (0 : E), C*‖x‖^alpha < eps :=
    hp.eventually (gt_mem_nhds heps)
  have hb : ∀ᶠ x : E in 𝓝 (0 : E), x ∈ ball (0 : E) R := Metric.ball_mem_nhds (0 : E) hR
  filter_upwards [self_mem_nhdsWithin,hs.filter_mono nhdsWithin_le_nhds,
    hb.filter_mono nhdsWithin_le_nhds] with x hx hsx hxR
  have hbound := herr x ⟨ball_subset_closedBall hxR,hx⟩
  have hn : inner ℝ N x ≤ ‖x‖ := by simpa only [hN,one_mul] using real_inner_le_norm N x
  have hh : |u x-a*inner ℝ N x| ≤ eps*‖x‖ :=
    (hbound.trans (mul_le_mul_of_nonneg_left hn (by positivity))).trans
      (mul_le_mul_of_nonneg_right hsx.le (norm_nonneg x))
  simpa only [hu0,sub_zero,_root_.smul_apply,innerSL_apply_apply,smul_eq_mul,Real.norm_eq_abs] using hh

theorem actual_quotient_identifies_within_derivative_four {N : E} (hN : ‖N‖=1)
    {u : E → ℝ} {L : E →L[ℝ] ℝ} {a C alpha R : ℝ}
    (hC : 0 ≤ C) (ha : 0 < alpha) (hR : 0 < R)
    (hL : HasFDerivWithinAt u L (actualFlatClosedUpperBallFour N R) 0)
    (herr : ∀ x ∈ actualFlatClosedUpperBallFour N R,
      |u x-a*inner ℝ N x| ≤ C*‖x‖^alpha*inner ℝ N x) :
    L=a • innerSL ℝ N := by
  have hh := (actual_quotient_remainder_hasFDerivWithinAt_four hN hC ha hR herr).mono
    (show actualFlatClosedUpperBallFour N R ⊆ {x : E | 0 ≤ inner ℝ N x} from fun _ hx => hx.2)
  exact (actual_closed_halfball_uniqueDiff_zero_four hN hR).eq hL hh

theorem actual_quotient_tangential_closure_jet_four
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U)
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U)
    {N : E} (hN : ‖N‖=1) {T phi : E → E} {G : E →L[ℝ] E}
    {R sigma a C alpha : ℝ} (hR : 0 < R) (hC : 0 ≤ C) (ha : 0 < alpha)
    (hT : DifferentiableAt ℝ T (phi 0)) (hphi : HasFDerivAt phi G 0)
    (hmap : MapsTo phi (actualFlatClosedUpperBallFour N R) (closure U))
    (herr : ∀ x ∈ actualFlatClosedUpperBallFour N R,
      |sigma*actualClosureTangentialResponseFour J T (phi x)-a*inner ℝ N x| ≤
        C*‖x‖^alpha*inner ℝ N x) :
    ∀ v : E,
      sigma*(J.hessian (phi 0) (G v) (T (phi 0))+
        J.derivative (phi 0) (fderiv ℝ T (phi 0) (G v)))=a*inner ℝ N v := by
  have hpoint : phi 0 ∈ closure U := hmap ⟨mem_closedBall_self hR.le,by simp⟩
  have hJd := closureJet_derivative_hasFDerivWithinAt hU hconv hu J hpoint
  have hresp := hJd.clm_apply hT.hasFDerivAt.hasFDerivWithinAt
  have hcomp := hresp.comp 0 hphi.hasFDerivWithinAt hmap
  have hscaled := hcomp.const_smul sigma
  have he := actual_quotient_identifies_within_derivative_four hN hC ha hR hscaled herr
  intro v
  have hev := congrArg (fun L : E →L[ℝ] ℝ => L v) he
  simpa only [_root_.smul_apply,smul_eq_mul,ContinuousLinearMap.comp_apply,
    _root_.add_apply,ContinuousLinearMap.flip_apply,innerSL_apply_apply,add_comm] using hev

theorem actual_quotient_identifies_normal_mixed_hessian_four
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U)
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U)
    {N : E} (hN : ‖N‖=1) {T phi : E → E} {G : E →L[ℝ] E}
    {R sigma a C alpha : ℝ} (hR : 0 < R) (hsigma : sigma ≠ 0)
    (hC : 0 ≤ C) (ha : 0 < alpha)
    (hT : DifferentiableAt ℝ T (phi 0)) (hphi : HasFDerivAt phi G 0)
    (hmap : MapsTo phi (actualFlatClosedUpperBallFour N R) (closure U))
    (herr : ∀ x ∈ actualFlatClosedUpperBallFour N R,
      |sigma*actualClosureTangentialResponseFour J T (phi x)-a*inner ℝ N x| ≤
        C*‖x‖^alpha*inner ℝ N x) :
    J.hessian (phi 0) (G N) (T (phi 0))=
      a/sigma-J.derivative (phi 0) (fderiv ℝ T (phi 0) (G N)) := by
  have hh := actual_quotient_tangential_closure_jet_four hU hconv hu J hN hR hC ha hT hphi hmap herr N
  rw [real_inner_self_eq_norm_sq,hN,one_pow,mul_one] at hh
  apply (eq_sub_iff_add_eq).mpr
  exact (eq_div_iff hsigma).mpr (by nlinarith [hh])

end PowerConvexity
