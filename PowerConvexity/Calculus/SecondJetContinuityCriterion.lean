import PowerConvexity.Calculus.EquicontinuousDerivativeFamilies
import PowerConvexity.Calculus.RealHessianRules
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! # A precise second-jet continuity criterion

A uniform spatial Hessian modulus upgrades joint first-jet continuity to joint
second-jet continuity. The uniform modulus is an explicit unresolved PDE estimate
when only individual classical Dirichlet regularity has been supplied.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open Set Metric Filter
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {T E : Type*} [TopologicalSpace T] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [ProperSpace E]

theorem realHessian_family_continuousAt_of_firstJet_modulus
    {u : T → E → ℝ} {t0 : T} {x0 : E} {R : ℝ} (hR : 0 < R)
    (hD : ∀ y ∈ closedBall x0 R,
      ContinuousAt (fun p : T × E => fderiv ℝ (u p.1) p.2) (t0,y))
    (hu : ∀ᶠ t in 𝓝 t0, ∀ y ∈ closedBall x0 R, ContDiffAt ℝ 2 (u t) y)
    {omega : ℝ → ℝ} (homega : Tendsto omega (𝓝 0) (𝓝 0))
    (hosc : ∀ᶠ t in 𝓝 t0, ∀ y ∈ closedBall x0 R,
      ‖realHessian (u t) y-realHessian (u t) x0‖ ≤ omega ‖y-x0‖) :
    ContinuousAt (fun p : T × E => realHessian (u p.1) p.2) (t0,x0) := by
  change ContinuousAt (fun p : T × E => fderiv ℝ (fderiv ℝ (u p.1)) p.2) (t0,x0)
  apply family_fderiv_continuousAt_of_uniform_oscillation (G := fun t => fderiv ℝ (u t)) hR hD
  · filter_upwards [hu] with t ht
    intro y hy
    exact ((ht y hy).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  · intro η hη
    have hnear : ∀ᶠ r in 𝓝 (0:ℝ), omega r < η := homega.eventually (Iio_mem_nhds hη)
    obtain ⟨δ,hδ,hsub⟩ := Metric.mem_nhds_iff.mp hnear
    let r := min R (δ/2)
    have hr : 0 < r := lt_min hR (by positivity)
    have hrR : r ≤ R := min_le_left _ _
    have hrδ : r < δ := (min_le_right _ _).trans_lt (by linarith)
    refine ⟨r,hr,hrR,?_⟩
    filter_upwards [hosc] with t ht
    intro y hy
    have hyR := (closedBall_subset_closedBall hrR) hy
    have hyr : ‖y-x0‖ ≤ r := by simpa only [mem_closedBall,dist_eq_norm] using hy
    have hin : ‖y-x0‖ ∈ ball (0:ℝ) δ := by
      simp only [mem_ball,dist_zero_right,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
      exact hyr.trans_lt hrδ
    exact (ht y hyR).trans (hsub hin).le

theorem realHessian_family_continuousAt_of_uniform_holder
    {u : T → E → ℝ} {t0 : T} {x0 : E} {R C α : ℝ} (hR : 0 < R)
    (hα : 0 < α)
    (hD : ∀ y ∈ closedBall x0 R,
      ContinuousAt (fun p : T × E => fderiv ℝ (u p.1) p.2) (t0,y))
    (hu : ∀ᶠ t in 𝓝 t0, ∀ y ∈ closedBall x0 R, ContDiffAt ℝ 2 (u t) y)
    (hH : ∀ᶠ t in 𝓝 t0, ∀ y ∈ closedBall x0 R,
      ‖realHessian (u t) y-realHessian (u t) x0‖ ≤ C*‖y-x0‖^α) :
    ContinuousAt (fun p : T × E => realHessian (u p.1) p.2) (t0,x0) := by
  have hc : Continuous (fun r : ℝ => C*|r|^α) :=
    continuous_const.mul ((Real.continuous_rpow_const hα.le).comp continuous_abs)
  have ht : Tendsto (fun r : ℝ => C*|r|^α) (𝓝 0) (𝓝 0) := by
    simpa only [abs_zero,Real.zero_rpow hα.ne',mul_zero] using (hc.continuousAt (x := 0)).tendsto
  apply realHessian_family_continuousAt_of_firstJet_modulus hR hD hu ht
  filter_upwards [hH] with t hh
  intro y hy
  simpa only [abs_of_nonneg (norm_nonneg _)] using hh y hy

end PowerConvexity
