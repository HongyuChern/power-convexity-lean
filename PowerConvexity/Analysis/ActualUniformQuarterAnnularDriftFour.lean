import PowerConvexity.Analysis.ActualUniformAnnularDriftPropagationFour

/-! # A quarter inner ball in the uniform annular propagation argument

The smaller inner ball fits into one fixed interior Harnack ball while its
center is allowed to move tangentially. All constants precede the center,
normal, coefficients, drift and actual response.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ

def actualClosedQuarterAnnulusFour (c : E) (R : ℝ) : Set E :=
  closedBall c R \ ball c (R/4)

theorem actual_mem_closed_quarter_annulus_four (c y : E) (R : ℝ) :
    y ∈ actualClosedQuarterAnnulusFour c R ↔ R/4 ≤ ‖y-c‖ ∧ ‖y-c‖ ≤ R := by
  simp only [actualClosedQuarterAnnulusFour,mem_diff,mem_closedBall,mem_ball,
    dist_eq_norm,not_lt]
  exact and_comm

theorem actual_mem_interior_quarter_annulus_four {c y : E} {R : ℝ}
    (hl : R/4 < ‖y-c‖) (hr : ‖y-c‖ < R) :
    y ∈ interior (actualClosedQuarterAnnulusFour c R) := by
  apply mem_interior_iff_mem_nhds.mpr
  have hn : ContinuousAt (fun z : E => ‖z-c‖) y :=
    (continuousAt_id.sub continuousAt_const).norm
  filter_upwards [continuousAt_const.eventually_lt hn hl,hn.eventually_lt_const hr]
    with z hzl hzr
  exact (actual_mem_closed_quarter_annulus_four c z R).mpr ⟨hzl.le,hzr.le⟩

theorem actual_quarter_annular_strict_subsolution_four
    (L : Bilin →ₗ[ℝ] ℝ) (c x : E)
    {ell T C R k : ℝ} (hell : 0 < ell) (hC : 0 ≤ C) (hR : 0 < R) (hk : 0 < k)
    (hchoice : 2*k*T+C*(1+2*k*R) < k^2*(ell/4)*R^2)
    (hlower : ell*‖x-c‖^2 ≤ L (realRankOneForm (x-c)))
    (htrace : L (realInnerForm (E := E)) ≤ T)
    (hrlow : R/4 ≤ ‖x-c‖) (hrhigh : ‖x-c‖ ≤ R) :
    C*(annularBarrier k R c x+‖fderiv ℝ (annularBarrier k R c) x‖) <
      L (realHessian (annularBarrier k R c) x) := by
  have hG : 0 < radialGaussian k c x := Real.exp_pos _
  have hlow2 : R^2 ≤ 16*‖x-c‖^2 := by nlinarith [norm_nonneg (x-c)]
  have hfirst : k^2*(ell/4)*R^2 ≤ 4*k^2*L (realRankOneForm (x-c)) := by
    have h1 := mul_le_mul_of_nonneg_left hlow2 (show 0 ≤ k^2*(ell/4) by positivity)
    have h2 := mul_le_mul_of_nonneg_left hlower (show 0 ≤ 4*k^2 by positivity)
    nlinarith
  have htrace' := mul_le_mul_of_nonneg_left htrace (show 0 ≤ 2*k by positivity)
  have hnorm : 2*k*‖x-c‖ ≤ 2*k*R :=
    mul_le_mul_of_nonneg_left hrhigh (by positivity)
  have hcoef : C*(1+2*k*‖x-c‖) <
      4*k^2*L (realRankOneForm (x-c))-2*k*L (realInnerForm (E := E)) := by
    have hCnorm := mul_le_mul_of_nonneg_left hnorm hC
    linarith
  have hstrict := mul_lt_mul_of_pos_left hcoef hG
  have hvle := annularBarrier_le_gaussian k R c x
  have hsmall := mul_le_mul_of_nonneg_left hvle hC
  rw [norm_fderiv_annularBarrier hk.le,realHessian_annularBarrier,
    map_sub L _ _,map_smul,map_smul,smul_eq_mul,smul_eq_mul]
  nlinarith

theorem actual_quarter_annular_drift_comparison_four
    {ell T C R k m : ℝ} (hell : 0 < ell) (hT : 0 ≤ T) (hC : 0 ≤ C) (hR : 0 < R)
    (hk : 0 < k) (hm : 0 < m)
    (hchoice : 2*k*T+C*(1+2*k*R) < k^2*(ell/4)*R^2)
    (c : E) (L : E → Bilin →ₗ[ℝ] ℝ) (b : E → E) {w : E → ℝ}
    (hwC : ContinuousOn w (closedBall c R)) (hw : ContDiffOn ℝ 2 w (ball c R))
    (hwn : ∀ x ∈ closedBall c R, 0 ≤ w x)
    (hinner : ∀ x ∈ closedBall c (R/4), m ≤ w x)
    (hL : ∀ x ∈ ball c R, HessianPositive (L x))
    (hlower : ∀ x ∈ ball c R, ∀ v : E, ell*‖v‖^2 ≤ L x (realRankOneForm v))
    (htrace : ∀ x ∈ ball c R, L x realInnerForm ≤ T)
    (hb : ∀ x ∈ ball c R, ‖b x‖ ≤ C)
    (hsub : ∀ x ∈ ball c R, L x (realHessian w x)+fderiv ℝ w x (b x) ≤ 0) :
    ∀ x ∈ actualClosedQuarterAnnulusFour c R, m*annularBarrier k R c x ≤ w x := by
  have hi : interior (actualClosedQuarterAnnulusFour c R) ⊆ ball c R := by
    intro x hx
    have hh := interior_mono
      (show actualClosedQuarterAnnulusFour c R ⊆ closedBall c R from diff_subset) hx
    rwa [interior_closedBall c hR.ne'] at hh
  apply compact_gradient_barrier_comparison ((isCompact_closedBall c R).diff isOpen_ball)
    (hwC.mono diff_subset) (annularBarrier_contDiff k R c (n := 2)).continuous.continuousOn
    (fun x hx => hw.contDiffAt (isOpen_ball.mem_nhds (hi hx)))
    (fun _ _ => (annularBarrier_contDiff k R c (n := 2)).contDiffAt) L
    (fun x hx => hL x (hi hx)) hC hm
  · intro x hx
    have hp := hsub x (hi hx)
    have hd : -fderiv ℝ w x (b x) ≤ C*‖fderiv ℝ w x‖ := by
      apply (neg_le_abs _).trans
      have hh := ((fderiv ℝ w x).le_opNorm (b x)).trans
        (mul_le_mul_of_nonneg_left (hb x (hi hx)) (norm_nonneg _))
      simpa only [Real.norm_eq_abs,mul_comm] using hh
    have hn := hwn x (ball_subset_closedBall (hi hx))
    nlinarith [mul_nonneg hC hn]
  · intro x hx
    have ha := (actual_mem_closed_quarter_annulus_four c x R).mp (interior_subset hx)
    exact actual_quarter_annular_strict_subsolution_four (L x) c x hell hC hR hk hchoice
      (hlower x (hi hx) (x-c)) (htrace x (hi hx)) ha.1 ha.2
  · intro x hx hnot
    have ha := (actual_mem_closed_quarter_annulus_four c x R).mp hx
    by_cases houter : ‖x-c‖=R
    · rw [annularBarrier_zero_on_sphere k R c x houter,mul_zero]
      exact hwn x hx.1
    · have hin : ‖x-c‖=R/4 := by
        by_contra hne
        exact hnot (actual_mem_interior_quarter_annulus_four
          (lt_of_le_of_ne ha.1 (Ne.symm hne)) (lt_of_le_of_ne ha.2 houter))
      have hsmall : x ∈ closedBall c (R/4) := by
        rw [mem_closedBall,dist_eq_norm,hin]
      exact (mul_le_mul_of_nonneg_left (annularBarrier_le_one hk.le R c x) hm.le).trans
        (by simpa only [mul_one] using hinner x hsmall)

theorem actual_uniform_quarter_annular_normal_propagation_four
    {ell T C R : ℝ} (hell : 0 < ell) (hT : 0 ≤ T) (hC : 0 ≤ C) (hR : 0 < R) :
    ∃ theta > 0, ∀ c N : E, ‖N‖=1 → ∀ L : E → Bilin →ₗ[ℝ] ℝ,
      ∀ b : E → E, ∀ w : E → ℝ,
      ContinuousOn w (closedBall c R) → ContDiffOn ℝ 2 w (ball c R) →
      (∀ x ∈ closedBall c R, 0 ≤ w x) →
      (∀ x ∈ ball c R, HessianPositive (L x)) →
      (∀ x ∈ ball c R, ∀ v : E, ell*‖v‖^2 ≤ L x (realRankOneForm v)) →
      (∀ x ∈ ball c R, L x realInnerForm ≤ T) →
      (∀ x ∈ ball c R, ‖b x‖ ≤ C) →
      (∀ x ∈ ball c R, L x (realHessian w x)+fderiv ℝ w x (b x) ≤ 0) →
      ∀ m > 0, (∀ x ∈ closedBall c (R/4), m ≤ w x) →
      ∀ d ∈ Icc (0 : ℝ) (R/2), m*theta*d ≤ w (c-(R-d) • N) := by
  obtain ⟨k,hk,hchoice⟩ := exists_annular_barrier_exponent
    (by positivity : 0 < ell/4) hT hC hR
  let theta := k*R*Real.exp (-k*R^2)
  refine ⟨theta,by dsimp only [theta]; positivity,?_⟩
  intro c N hN L b w hwC hw hwn hL hlower htrace hb hsub m hm hinner d hd
  have hRd : 0 ≤ R-d := by linarith [hd.1,hd.2]
  have hn : ‖(c-(R-d) • N)-c‖=R-d := by
    rw [show c-(R-d) • N-c=(-(R-d)) • N by module,
      norm_smul,Real.norm_eq_abs,abs_neg,abs_of_nonneg hRd,hN,mul_one]
  have ha : c-(R-d) • N ∈ actualClosedQuarterAnnulusFour c R := by
    rw [actual_mem_closed_quarter_annulus_four,hn]
    exact ⟨by linarith [hd.2],by linarith [hd.1]⟩
  have hbar := actual_quarter_annular_drift_comparison_four hell hT hC hR hk hm hchoice
    c L b hwC hw hwn hinner hL hlower htrace hb hsub _ ha
  have hlo := mul_le_mul_of_nonneg_left
    (actual_annular_barrier_normal_lower_four hN c hk.le hR hd) hm.le
  calc
    m*theta*d=m*((k*R*Real.exp (-k*R^2))*d) := by dsimp only [theta]; ring
    _ ≤ m*annularBarrier k R c (c-(R-d) • N) := hlo
    _ ≤ w (c-(R-d) • N) := hbar

end PowerConvexity
