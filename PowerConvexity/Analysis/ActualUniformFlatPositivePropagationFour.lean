import PowerConvexity.Analysis.ActualUniformBoundaryPropagationGeometryFour
import PowerConvexity.Analysis.ActualUniformLocalSourceHarnackFour
import PowerConvexity.Analysis.ActualUniformNormalSourceCorrectionFour
import PowerConvexity.Analysis.ActualFlatEllipticCompactnessFour

/-! # Uniform boundary-distance propagation for the same actual response

One fixed interior Harnack ball supplies every moving inner quarter ball.
The actual bounded-source equation is then compared on each tangent ball.
The resulting constants precede the normal, coefficient, drift, source and
response. No coefficient Holder modulus enters the conclusion.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_uniform_flat_positive_propagation_four {Lambda : ℝ} (hLambda : 1 ≤ Lambda) :
    ∃ kappa > 0, kappa ≤ (1/4 : ℝ) ∧ ∃ K > 0,
      ∀ N : E, ‖N‖=1 →
      ∀ A : NormalizedEllipticCoeff (2+2) (actualFlatUpperBallFour N 1), A.1.Λ ≤ Lambda →
      (∀ i j, ContDiffOn ℝ 1 (fun x => A.1.a x i j) (actualFlatUpperBallFour N 1)) →
      (∀ x ∈ actualFlatUpperBallFour N 1, (A.1.a x).PosDef) →
      ∀ b : E → E, ContinuousOn b (actualFlatUpperBallFour N 1) →
      (∀ x ∈ actualFlatUpperBallFour N 1, actualCoefficientColumnDivergenceFour A.1.a x=b x) →
      (∀ x ∈ actualFlatUpperBallFour N 1, ‖b x‖ ≤ 1/2) →
      ∀ f u : E → ℝ, ContinuousOn f (actualFlatUpperBallFour N 1) →
      ContDiffOn ℝ 2 u (actualFlatUpperBallFour N 1) →
      ContinuousOn u (actualFlatClosedUpperBallFour N 1) →
      (∀ x ∈ actualFlatClosedUpperBallFour N 1, 0 ≤ u x) →
      ∀ M : ℝ, (∀ x ∈ actualFlatUpperBallFour N 1, u x ≤ M) →
      ∀ F > 0, (∀ x ∈ actualFlatUpperBallFour N 1, |f x| ≤ F) →
      (∀ x ∈ actualFlatUpperBallFour N 1,
        (∑ i, ∑ j, A.1.a x i j*euclideanHessian u x i j)+fderiv ℝ u x (b x) = -f x) →
      ∀ x ∈ actualFlatClosedUpperBallFour N (1/64),
        (kappa*u ((1/4 : ℝ) • N)-K*F)*inner ℝ N x ≤ u x := by
  let R : ℝ := 1/4
  let r : ℝ := 3*R/4
  have hR : 0 < R := by norm_num [R]
  have hr : 0 < r := by norm_num [r,R]
  obtain ⟨theta,htheta,hprop⟩ := actual_uniform_source_quarter_annular_propagation_four
    («E» := E) (ell := 1) (T := 4*Lambda) (C := 1/2) (R := R)
    (by norm_num) (by linarith) (by norm_num) (by norm_num) hR (by norm_num [R])
  let H := actualUniformHarnackFactorFour Lambda
  have hH : 0 < H := actual_uniform_harnack_factor_positive_four Lambda
  let kappa := min (theta/H) (1/4 : ℝ)
  let K := 2*theta*r^2+2
  have hkappa : 0 < kappa := lt_min (div_pos htheta hH) (by norm_num)
  have hkappaH : kappa ≤ theta/H := min_le_left _ _
  refine ⟨kappa,hkappa,min_le_right _ _,K,by dsimp only [K]; positivity,?_⟩
  intro N hN A hAupper hA hpos b hb hdiv hbb f u hf hu huC hun M hub F hF hfb hpde
  let U := actualFlatUpperBallFour N 1
  let P := R • N
  let Q := fun x => matrixHessianContraction (fun i => EuclideanSpace.single i (1 : ℝ)) (A.1.a x)
  have hU : IsOpen U := actualFlatUpperBallFour_isOpen N 1
  have hUC : U ⊆ actualFlatClosedUpperBallFour N 1 := fun x hx =>
    ⟨ball_subset_closedBall hx.1,(show 0 < inner ℝ N x from hx.2).le⟩
  have haC (i j : Fin (2+2)) : ContinuousOn (fun x => A.1.a x i j) U := (hA i j).continuousOn
  have htrace (x : E) (hx : x ∈ U) : 1 ≤ (A.1.a x).trace := by
    have hh := actual_elliptic_matrix_trace_lower_four hU A.1 haC x hx
    rw [A.property,mul_one] at hh
    linarith
  have hQpos (x : E) (hx : x ∈ U) : HessianPositive (Q x) :=
    matrixHessianContraction_positive _ (hpos x hx).posSemidef
  have hQlow (x : E) (hx : x ∈ U) (v : E) : 1*‖v‖^2 ≤ Q x (realRankOneForm v) := by
    rw [show Q x=matrixHessianContraction (fun i => EuclideanSpace.single i (1 : ℝ)) (A.1.a x) from rfl,
      actual_matrix_contraction_rankOne_energy_four]
    simpa only [A.property] using (actual_elliptic_bounds_pointwise_two hU A.1 haC x hx v).1
  have hQtrace (x : E) (hx : x ∈ U) : Q x realInnerForm ≤ 4*Lambda :=
    (actual_elliptic_matrix_contraction_trace_upper_four hU A.1 haC x hx).trans (by linarith)
  have hQu (x : E) (hx : x ∈ U) : Q x (realHessian u x)+fderiv ℝ u x (b x) ≤ F := by
    rw [show Q x=matrixHessianContraction (fun i => EuclideanSpace.single i (1 : ℝ)) (A.1.a x) from rfl,
      actual_matrix_contraction_euclideanHessian_four _ (hu.contDiffAt (hU.mem_nhds hx)),hpde x hx]
    exact (neg_le_abs _).trans (hfb x hx)
  have hfixed : closedBall P r ⊆ U := actual_fixed_normal_harnack_ball_maps_four hN hR (by norm_num [R])
  have hP : P ∈ ball P (r/2) := mem_ball_self (by positivity)
  have hPU : P ∈ U := hfixed (mem_closedBall_self hr.le)
  have huP : 0 ≤ u P := hun P (hUC hPU)
  have hhar := actual_local_classical_source_harnack_four hU A hAupper hF hA hb
    hdiv htrace hbb hf hu (fun x hx => hun x (hUC hx)) hub hfb hpde hr hfixed
    (by norm_num [r,R] : r*(1/2 : ℝ) ≤ 1/2)
  let m := u P/H-2*r^2*F
  have hcoeff : kappa*u P-K*F ≤ theta*m-2*F := by
    have hh := mul_le_mul_of_nonneg_right hkappaH huP
    dsimp only [K,m]
    calc
      kappa*u P-(2*theta*r^2+2)*F ≤ (theta/H)*u P-(2*theta*r^2+2)*F := by linarith
      _ = theta*(u P/H-2*r^2*F)-2*F := by ring
  intro x hx
  let d := inner ℝ N x
  have hd0 : 0 ≤ d := hx.2
  have hxnorm : ‖x‖ ≤ 1/64 := by simpa only [mem_closedBall,dist_zero_right] using hx.1
  have hxclosed : x ∈ actualFlatClosedUpperBallFour N 1 :=
    ⟨closedBall_subset_closedBall (by norm_num) hx.1,hx.2⟩
  change (kappa*u P-K*F)*d ≤ u x
  by_cases hm : 0 < m
  · let c := x-d • N+R • N
    have hproj := actual_flat_projection_geometry_four hN x
    have hc : inner ℝ N c=R := by
      change inner ℝ N (x-d • N+R • N)=R
      rw [inner_add_right,hproj.1,inner_smul_right,real_inner_self_eq_norm_sq,hN,one_pow,mul_one,zero_add]
    have hcP : ‖c-R • N‖ ≤ R/16 := by
      have he : c-R • N=x-d • N := by dsimp only [c]; abel
      rw [he]
      exact hproj.2.trans (by dsimp only [R]; linarith)
    have hclosed := actual_moving_tangent_closed_ball_maps_four hN hR (by norm_num [R]) hc hcP
    have hopen := actual_moving_tangent_open_ball_maps_four hN hR (by norm_num [R]) hc hcP
    have hinner (y : E) (hy : y ∈ closedBall c (R/4)) : m ≤ u y := by
      have hyfixed := actual_moving_quarter_ball_in_fixed_half_four hR hcP hy
      have hh := hhar P hP y hyfixed
      have he : u P/H ≤ u y+2*(r^2*F) :=
        (div_le_iff₀ hH).mpr (by simpa only [H,mul_comm] using hh)
      dsimp only [m]
      linarith
    have hd : d ∈ Icc (0 : ℝ) (R/2) := by
      have hi : d ≤ ‖x‖ := by simpa only [hN,one_mul] using real_inner_le_norm N x
      exact ⟨hd0,by dsimp only [R]; linarith⟩
    have hh := hprop c N hN hc Q b u (huC.mono hclosed) (hu.mono hopen)
      (fun y hy => hun y (hclosed hy)) (fun y hy => hQpos y (hopen hy))
      (fun y hy v => hQlow y (hopen hy) v) (fun y hy => hQtrace y (hopen hy))
      (fun y hy => hbb y (hopen hy)) F hF.le (fun y hy => hQu y (hopen hy)) m hm hinner d hd
    have he : c-(R-d) • N=x := by dsimp only [c]; module
    rw [he,div_one] at hh
    have hmul := mul_le_mul_of_nonneg_right hcoeff hd0
    nlinarith
  · have hm0 : m ≤ 0 := le_of_not_gt hm
    have hn : theta*m-2*F ≤ 0 := by nlinarith [mul_nonpos_of_nonneg_of_nonpos htheta.le hm0]
    exact (mul_nonpos_of_nonpos_of_nonneg (hcoeff.trans hn) hd0).trans (hun x hxclosed)

end PowerConvexity
