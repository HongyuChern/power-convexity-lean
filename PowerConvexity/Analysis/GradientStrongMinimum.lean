import PowerConvexity.Analysis.TangentBall
import PowerConvexity.Analysis.ContactPropagation
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Classical strong minimum principle with a gradient term

The contraction acts on the actual real Frechet Hessian.  Local uniform
ellipticity and bounded zero/first-order coefficients are explicit data;
the analytic zero propagation is proved by an annular barrier, not assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Metric Set
open scoped ContDiff Topology

namespace PowerConvexity
open CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

theorem zero_propagation_gradient_on_ball {w : E → ℝ} {x : E} {δ ell Λ C : ℝ}
    (hδ : 0 < δ) (hell : 0 < ell) (hΛ : 0 ≤ Λ) (hC : 0 ≤ C)
    (hw : ∀ y ∈ ball x δ, ContDiffAt ℝ 2 w y)
    (hwn : ∀ y ∈ ball x δ, 0 ≤ w y) (hwx : w x = 0)
    (L : E → (E →L[ℝ] E →L[ℝ] ℝ) →ₗ[ℝ] ℝ)
    (hL : ∀ y ∈ ball x δ, HessianPositive (L y))
    (hlower : ∀ y ∈ ball x δ, ∀ v : E, ell * ‖v‖^2 ≤ L y (realRankOneForm v))
    (htrace : ∀ y ∈ ball x δ, L y (realInnerForm (E := E)) ≤ Λ)
    (hsub : ∀ y ∈ ball x δ,
      L y (realHessian w y) ≤ C * (w y + ‖fderiv ℝ w y‖)) :
    ∀ y ∈ ball x (δ/4), w y = 0 := by
  intro y hy
  have hyδ : y ∈ ball x δ := ball_subset_ball (by linarith) hy
  by_contra hy0
  have hypos : 0 < w y := lt_of_le_of_ne (hwn y hyδ) (Ne.symm hy0)
  let Z : Set E := closedBall x (δ/2) ∩ w ⁻¹' ({0} : Set ℝ)
  have hhalf : closedBall x (δ/2) ⊆ ball x δ := closedBall_subset_ball (by linarith)
  have hwc : ContinuousOn w (closedBall x (δ/2)) :=
    fun z hz => (hw z (hhalf hz)).continuousAt.continuousWithinAt
  have hZclosed : IsClosed Z :=
    hwc.preimage_isClosed_of_isClosed isClosed_closedBall isClosed_singleton
  have hxZ : x ∈ Z := ⟨mem_closedBall_self (by linarith), hwx⟩
  have hZnonempty : Z.Nonempty := ⟨x, hxZ⟩
  have hyZ : y ∉ Z := fun h => hy0 h.2
  let R := infDist y Z
  have hR : 0 < R := hZclosed.notMem_iff_infDist_pos hZnonempty |>.mp hyZ
  obtain ⟨z, hz, hzd⟩ := hZclosed.exists_infDist_eq_dist hZnonempty y
  have hRle : R ≤ dist y x := infDist_le_dist_of_mem hxZ
  have hylt : dist y x < δ/4 := hy
  have hballhalf : closedBall y R ⊆ closedBall x (δ/2) := by
    intro p hp
    have hpR : dist p y ≤ R := hp
    have ht := dist_triangle p y x
    change dist p x ≤ δ/2
    linarith
  have hballδ : closedBall y R ⊆ ball x δ := hballhalf.trans hhalf
  have hzR : ‖z-y‖ = R := by
    change R = dist y z at hzd
    rw [dist_comm, dist_eq_norm] at hzd
    exact hzd.symm
  have hpositive : ∀ p ∈ ball y R, 0 < w p := by
    intro p hp
    have hpd := hballδ (ball_subset_closedBall hp)
    have hpnot : p ∉ Z := notMem_of_dist_lt_infDist (by
      change dist y p < R
      change dist p y < R at hp
      simpa only [dist_comm] using hp)
    have hpnonzero : w p ≠ 0 := fun he => hpnot ⟨hballhalf (ball_subset_closedBall hp), he⟩
    exact lt_of_le_of_ne (hwn p hpd) (Ne.symm hpnonzero)
  have hzδ : z ∈ ball x δ := hhalf hz.1
  have hnear : ∀ᶠ p in 𝓝 z, 0 ≤ w p :=
    Filter.Eventually.mono (isOpen_ball.mem_nhds hzδ) fun p hp => hwn p hp
  exact positive_ball_cannot_touch_zero hR hell hΛ hC
    (fun p hp => (hw p (hballδ hp)).continuousAt.continuousWithinAt)
    (fun p hp => hw p (hballδ hp)) hpositive
    (fun p hp => hwn p (hballδ hp)) hzR hz.2 hnear L
    (fun p hp => hL p (hballδ hp))
    (fun p hp => hlower p (hballδ hp))
    (fun p hp => htrace p (hballδ hp))
    (fun p hp => hsub p (hballδ hp))

/-- A local uniform hypothesis appropriate for continuous strictly elliptic
coefficient fields.  C controls both the zero-order and gradient terms. -/
def LocallyUniformGradientSupersolution (U : Set E) (w : E → ℝ)
    (L : E → (E →L[ℝ] E →L[ℝ] ℝ) →ₗ[ℝ] ℝ) : Prop :=
  ∀ x ∈ U, ∃ δ ell Λ C : ℝ, 0 < δ ∧ 0 < ell ∧ 0 ≤ Λ ∧ 0 ≤ C ∧
    ball x δ ⊆ U ∧
    (∀ y ∈ ball x δ, HessianPositive (L y)) ∧
    (∀ y ∈ ball x δ, ∀ v : E, ell * ‖v‖^2 ≤ L y (realRankOneForm v)) ∧
    (∀ y ∈ ball x δ, L y (realInnerForm (E := E)) ≤ Λ) ∧
    (∀ y ∈ ball x δ, L y (realHessian w y) ≤ C * (w y + ‖fderiv ℝ w y‖))

theorem gradient_supersolution_local_zero {U : Set E} {w : E → ℝ}
    (hw : ∀ x ∈ U, ContDiffAt ℝ 2 w x) (hwn : ∀ x ∈ U, 0 ≤ w x)
    (L : E → (E →L[ℝ] E →L[ℝ] ℝ) →ₗ[ℝ] ℝ)
    (hL : LocallyUniformGradientSupersolution U w L)
    {x : E} (hx : x ∈ U) (hwx : w x = 0) : ∀ᶠ y in 𝓝 x, w y = 0 := by
  obtain ⟨δ, ell, Λ, C, hδ, hell, hΛ, hC, hball, hpos, hlower, htrace, hsub⟩ := hL x hx
  have hz := zero_propagation_gradient_on_ball hδ hell hΛ hC
    (fun y hy => hw y (hball hy)) (fun y hy => hwn y (hball hy)) hwx L hpos hlower htrace hsub
  exact Filter.Eventually.mono (ball_mem_nhds x (by positivity : 0 < δ/4)) hz

theorem strong_minimum_gradient_positive {U : Set E}
    (hU : IsOpen U) (hconn : IsPreconnected U) {w : E → ℝ}
    (hw : ∀ x ∈ U, ContDiffAt ℝ 2 w x) (hwn : ∀ x ∈ U, 0 ≤ w x)
    (L : E → (E →L[ℝ] E →L[ℝ] ℝ) →ₗ[ℝ] ℝ)
    (hL : LocallyUniformGradientSupersolution U w L)
    (hanchor : ∃ x ∈ U, 0 < w x) : ∀ x ∈ U, 0 < w x := by
  apply positive_on_connected_of_local_zero_propagation hU hconn
    (fun x hx => (hw x hx).continuousAt.continuousWithinAt) hwn
    (fun x hx hx0 => gradient_supersolution_local_zero hw hwn L hL hx hx0) hanchor

theorem strong_minimum_gradient_zero {U : Set E}
    (hU : IsOpen U) (hconn : IsPreconnected U) {w : E → ℝ}
    (hw : ∀ x ∈ U, ContDiffAt ℝ 2 w x) (hwn : ∀ x ∈ U, 0 ≤ w x)
    (L : E → (E →L[ℝ] E →L[ℝ] ℝ) →ₗ[ℝ] ℝ)
    (hL : LocallyUniformGradientSupersolution U w L)
    {x : E} (hx : x ∈ U) (hwx : w x = 0) : ∀ y ∈ U, w y = 0 := by
  intro y hy
  by_contra hy0
  have hypos : 0 < w y := lt_of_le_of_ne (hwn y hy) (Ne.symm hy0)
  have hp := strong_minimum_gradient_positive hU hconn hw hwn L hL ⟨y, hy, hypos⟩ x hx
  rw [hwx] at hp
  exact (lt_irrefl 0) hp

end PowerConvexity
