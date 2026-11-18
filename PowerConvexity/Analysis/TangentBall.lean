import PowerConvexity.Analysis.AnnularBarrier
import PowerConvexity.Analysis.BarrierContact
import Mathlib.Topology.MetricSpace.ProperSpace

/-! # A positive ball cannot touch an interior zero of a gradient supersolution -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Metric Set
open scoped ContDiff Topology

namespace PowerConvexity
open CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

def closedAnnulus (c : E) (R : ℝ) : Set E := closedBall c R \ ball c (R/2)

theorem mem_closedAnnulus (c y : E) (R : ℝ) :
    y ∈ closedAnnulus c R ↔ R/2 ≤ ‖y-c‖ ∧ ‖y-c‖ ≤ R := by
  simp only [closedAnnulus, mem_diff, mem_closedBall, mem_ball, dist_eq_norm, not_lt]
  exact and_comm

theorem isCompact_closedAnnulus (c : E) (R : ℝ) : IsCompact (closedAnnulus c R) :=
  (isCompact_closedBall c R).diff isOpen_ball

theorem mem_interior_closedAnnulus {c y : E} {R : ℝ}
    (hl : R/2 < ‖y-c‖) (hr : ‖y-c‖ < R) : y ∈ interior (closedAnnulus c R) := by
  apply mem_interior_iff_mem_nhds.mpr
  have hn : ContinuousAt (fun z : E => ‖z-c‖) y :=
    (continuousAt_id.sub continuousAt_const).norm
  filter_upwards [continuousAt_const.eventually_lt hn hl, hn.eventually_lt_const hr]
    with z hzl hzr
  exact (mem_closedAnnulus c z R).mpr ⟨hzl.le, hzr.le⟩

theorem annularBarrier_le_one {k : ℝ} (hk : 0 ≤ k) (R : ℝ) (c x : E) :
    annularBarrier k R c x ≤ 1 := by
  apply (annularBarrier_le_gaussian k R c x).trans
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hk) (sq_nonneg _))

/-- Classical tangent-ball contradiction.  The supersolution may contain both
C*w and C*|Dw|.  The surrounding nonnegative neighborhood is explicit. -/
theorem positive_ball_cannot_touch_zero {w : E → ℝ} {c x : E} {R ell Λ C : ℝ}
    (hR : 0 < R) (hell : 0 < ell) (hΛ : 0 ≤ Λ) (hC : 0 ≤ C)
    (hwc : ContinuousOn w (closedBall c R))
    (hw : ∀ y ∈ closedBall c R, ContDiffAt ℝ 2 w y)
    (hpos : ∀ y ∈ ball c R, 0 < w y)
    (hwn : ∀ y ∈ closedBall c R, 0 ≤ w y)
    (hx : ‖x-c‖ = R) (hwx : w x = 0) (hne : ∀ᶠ y in 𝓝 x, 0 ≤ w y)
    (L : E → (E →L[ℝ] E →L[ℝ] ℝ) →ₗ[ℝ] ℝ)
    (hL : ∀ y ∈ closedBall c R, HessianPositive (L y))
    (hlower : ∀ y ∈ closedBall c R, ∀ v : E,
      ell * ‖v‖^2 ≤ L y (realRankOneForm v))
    (htrace : ∀ y ∈ closedBall c R, L y (realInnerForm (E := E)) ≤ Λ)
    (hsub : ∀ y ∈ closedBall c R,
      L y (realHessian w y) ≤ C * (w y + ‖fderiv ℝ w y‖)) : False := by
  obtain ⟨k, hk, hchoice⟩ := exists_annular_barrier_exponent hell hΛ hC hR
  have hsmall : closedBall c (R/2) ⊆ ball c R := closedBall_subset_ball (by linarith)
  have hsmallclosed : closedBall c (R/2) ⊆ closedBall c R :=
    hsmall.trans ball_subset_closedBall
  obtain ⟨z, hz, hzmin⟩ := (isCompact_closedBall c (R/2)).exists_isMinOn
    ⟨c, mem_closedBall_self (by linarith)⟩ (hwc.mono hsmallclosed)
  have heps : 0 < w z := hpos z (hsmall hz)
  have hcomp : ∀ y ∈ closedAnnulus c R, w z * annularBarrier k R c y ≤ w y := by
    apply compact_gradient_barrier_comparison (isCompact_closedAnnulus c R)
      (hwc.mono diff_subset) (annularBarrier_contDiff k R c (n := 2)).continuous.continuousOn
      (fun y hy => hw y (interior_subset hy).1)
      (fun _ _ => (annularBarrier_contDiff k R c (n := 2)).contDiffAt) L
      (fun y hy => hL y (interior_subset hy).1) hC heps
      (fun y hy => hsub y (interior_subset hy).1)
    · intro y hy
      have hya := (mem_closedAnnulus c y R).mp (interior_subset hy)
      have hyb : y ∈ closedBall c R := (interior_subset hy).1
      exact annularBarrier_strict_subsolution (L y) c y hell hC hR hk hchoice
        (hlower y hyb (y-c)) (htrace y hyb) hya.1 hya.2
    · intro y hy hni
      have hya := (mem_closedAnnulus c y R).mp hy
      by_cases houter : ‖y-c‖ = R
      · rw [annularBarrier_zero_on_sphere k R c y houter, mul_zero]
        exact hwn y hy.1
      · have hinner : ‖y-c‖ = R/2 := by
          by_contra hneinner
          have hleft : R/2 < ‖y-c‖ := lt_of_le_of_ne hya.1 (Ne.symm hneinner)
          have hright : ‖y-c‖ < R := lt_of_le_of_ne hya.2 houter
          exact hni (mem_interior_closedAnnulus hleft hright)
        have hymem : y ∈ closedBall c (R/2) := by
          rw [mem_closedBall, dist_eq_norm, hinner]
        have hymin : w z ≤ w y := hzmin hymem
        have hbar := mul_le_mul_of_nonneg_left (annularBarrier_le_one hk.le R c y) heps.le
        have hbarle : w z * annularBarrier k R c y ≤ w z := by
          simpa only [mul_one] using hbar
        exact hbarle.trans hymin
  have hxb : x ∈ closedBall c R := by rw [mem_closedBall, dist_eq_norm, hx]
  exact annular_zero_contact_impossible hk hR heps
    ((hw x hxb).differentiableAt (by norm_num)) hwx hne hx
    (fun y hyl hyr => hcomp y ((mem_closedAnnulus c y R).mpr ⟨hyl, hyr⟩))

end PowerConvexity
