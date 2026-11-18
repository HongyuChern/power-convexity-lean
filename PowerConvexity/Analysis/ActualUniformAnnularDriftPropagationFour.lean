import PowerConvexity.Analysis.TangentBall

/-! # Quantitative normal propagation from an actual positive inner ball

The exponent and normal slope are chosen before the coefficient, drift,
solution, center and normal. The proof uses the genuine Gaussian annular
barrier and the classical equation; no coefficient continuity modulus or
boundary differentiability of the response is required.
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

theorem actual_annular_drift_comparison_four
    {ell T C R k m : ℝ} (hell : 0<ell) (hT : 0≤T) (hC : 0≤C) (hR : 0<R)
    (hk : 0<k) (hm : 0<m)
    (hchoice : 2*k*T+C*(1+2*k*R)<k^2*ell*R^2)
    (c : E) (L : E → Bilin →ₗ[ℝ] ℝ) (b : E → E) {w : E → ℝ}
    (hwC : ContinuousOn w (closedBall c R)) (hw : ContDiffOn ℝ 2 w (ball c R))
    (hwn : ∀ x∈closedBall c R, 0≤w x)
    (hinner : ∀ x∈closedBall c (R/2), m≤w x)
    (hL : ∀ x∈ball c R, HessianPositive (L x))
    (hlower : ∀ x∈ball c R, ∀ v : E, ell*‖v‖^2≤L x (realRankOneForm v))
    (htrace : ∀ x∈ball c R, L x realInnerForm≤T)
    (hb : ∀ x∈ball c R, ‖b x‖≤C)
    (hsub : ∀ x∈ball c R, L x (realHessian w x)+fderiv ℝ w x (b x)≤0) :
    ∀ x∈closedAnnulus c R, m*annularBarrier k R c x≤w x := by
  have hi : interior (closedAnnulus c R) ⊆ ball c R := by
    intro x hx
    have hh := interior_mono (show closedAnnulus c R ⊆ closedBall c R from diff_subset) hx
    rwa [interior_closedBall c hR.ne'] at hh
  apply compact_gradient_barrier_comparison (isCompact_closedAnnulus c R)
    (hwC.mono diff_subset) (annularBarrier_contDiff k R c (n := 2)).continuous.continuousOn
    (fun x hx => hw.contDiffAt (isOpen_ball.mem_nhds (hi hx)))
    (fun _ _ => (annularBarrier_contDiff k R c (n := 2)).contDiffAt) L
    (fun x hx => hL x (hi hx)) hC hm
  · intro x hx
    have hp := hsub x (hi hx)
    have hd : -fderiv ℝ w x (b x)≤C*‖fderiv ℝ w x‖ := by
      apply (neg_le_abs _).trans
      have hh := ((fderiv ℝ w x).le_opNorm (b x)).trans
        (mul_le_mul_of_nonneg_left (hb x (hi hx)) (norm_nonneg _))
      simpa only [Real.norm_eq_abs,mul_comm] using hh
    have hn := hwn x (ball_subset_closedBall (hi hx))
    nlinarith [mul_nonneg hC hn]
  · intro x hx
    have ha := (mem_closedAnnulus c x R).mp (interior_subset hx)
    exact annularBarrier_strict_subsolution (L x) c x hell hC hR hk hchoice
      (hlower x (hi hx) (x-c)) (htrace x (hi hx)) ha.1 ha.2
  · intro x hx hnot
    have ha := (mem_closedAnnulus c x R).mp hx
    by_cases houter : ‖x-c‖=R
    · rw [annularBarrier_zero_on_sphere k R c x houter,mul_zero]
      exact hwn x hx.1
    · have hin : ‖x-c‖=R/2 := by
        by_contra hne
        exact hnot (mem_interior_closedAnnulus
          (lt_of_le_of_ne ha.1 (Ne.symm hne)) (lt_of_le_of_ne ha.2 houter))
      have hsmall : x∈closedBall c (R/2) := by
        rw [mem_closedBall,dist_eq_norm,hin]
      exact (mul_le_mul_of_nonneg_left (annularBarrier_le_one hk.le R c x) hm.le).trans
        (by simpa only [mul_one] using hinner x hsmall)

theorem actual_annular_barrier_normal_lower_four {N : E} (hN : ‖N‖=1)
    (c : E) {k R d : ℝ} (hk : 0≤k) (hR : 0<R) (hd : d∈Icc (0 : ℝ) (R/2)) :
    (k*R*Real.exp (-k*R^2))*d≤annularBarrier k R c (c-(R-d) • N) := by
  have hRd : 0≤R-d := by linarith [hd.1,hd.2]
  have hn : ‖(c-(R-d) • N)-c‖=R-d := by
    rw [show c-(R-d) • N-c=(-(R-d)) • N by module,
      norm_smul,Real.norm_eq_abs,abs_neg,abs_of_nonneg hRd,hN,mul_one]
  let delta := k*(R^2-(R-d)^2)
  have hdelta : k*R*d≤delta := by
    dsimp only [delta]
    have hh : 0≤k*d*(R-d) := mul_nonneg (mul_nonneg hk hd.1) hRd
    nlinarith
  have he : Real.exp (-k*(R-d)^2)=Real.exp (-k*R^2)*Real.exp delta := by
    rw [← Real.exp_add]
    congr 1
    dsimp only [delta]
    ring
  have hE := mul_le_mul_of_nonneg_left (Real.add_one_le_exp delta) (Real.exp_pos (-k*R^2)).le
  have hD := mul_le_mul_of_nonneg_left hdelta (Real.exp_pos (-k*R^2)).le
  unfold annularBarrier radialGaussian
  rw [hn,he]
  nlinarith

theorem actual_uniform_annular_drift_normal_propagation_four
    {ell T C R : ℝ} (hell : 0<ell) (hT : 0≤T) (hC : 0≤C) (hR : 0<R) :
    ∃ theta>0, ∀ c N : E, ‖N‖=1 → ∀ L : E → Bilin →ₗ[ℝ] ℝ,
      ∀ b : E → E, ∀ w : E → ℝ,
      ContinuousOn w (closedBall c R) → ContDiffOn ℝ 2 w (ball c R) →
      (∀ x∈closedBall c R, 0≤w x) →
      (∀ x∈ball c R, HessianPositive (L x)) →
      (∀ x∈ball c R, ∀ v : E, ell*‖v‖^2≤L x (realRankOneForm v)) →
      (∀ x∈ball c R, L x realInnerForm≤T) →
      (∀ x∈ball c R, ‖b x‖≤C) →
      (∀ x∈ball c R, L x (realHessian w x)+fderiv ℝ w x (b x)≤0) →
      ∀ m>0, (∀ x∈closedBall c (R/2), m≤w x) →
      ∀ d∈Icc (0 : ℝ) (R/2), m*theta*d≤w (c-(R-d) • N) := by
  obtain ⟨k,hk,hchoice⟩ := exists_annular_barrier_exponent hell hT hC hR
  let theta := k*R*Real.exp (-k*R^2)
  refine ⟨theta,by dsimp only [theta]; positivity,?_⟩
  intro c N hN L b w hwC hw hwn hL hlower htrace hb hsub m hm hinner d hd
  have hRd : 0≤R-d := by linarith [hd.1,hd.2]
  have hn : ‖(c-(R-d) • N)-c‖=R-d := by
    rw [show c-(R-d) • N-c=(-(R-d)) • N by module,
      norm_smul,Real.norm_eq_abs,abs_neg,abs_of_nonneg hRd,hN,mul_one]
  have ha : c-(R-d) • N∈closedAnnulus c R := by
    rw [mem_closedAnnulus,hn]
    exact ⟨by linarith [hd.2],by linarith [hd.1]⟩
  have hbar := actual_annular_drift_comparison_four hell hT hC hR hk hm hchoice c L b
    hwC hw hwn hinner hL hlower htrace hb hsub _ ha
  have hlo := mul_le_mul_of_nonneg_left (actual_annular_barrier_normal_lower_four hN c hk.le hR hd) hm.le
  calc
    m*theta*d=m*((k*R*Real.exp (-k*R^2))*d) := by dsimp only [theta]; ring
    _ ≤ m*annularBarrier k R c (c-(R-d) • N) := hlo
    _ ≤ w (c-(R-d) • N) := hbar

end PowerConvexity
