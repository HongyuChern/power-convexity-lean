import PowerConvexity.Analysis.GradientStrongMinimum

/-! # Strong minimum propagation through smooth supersolution approximants

The limiting function needs differentiability, not a C2 extension. Uniform
ellipticity and differential-inequality constants apply to all approximants.
Pointwise convergence and domination suffice for the annular comparison.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric Filter
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

theorem positive_ball_cannot_touch_zero_of_approximation
    {w : E → ℝ} (wseq : ℕ → E → ℝ) {c x : E} {R ell Λ C : ℝ}
    (hR : 0 < R) (hell : 0 < ell) (hΛ : 0 ≤ Λ) (hC : 0 ≤ C)
    (hwc : ContinuousOn w (closedBall c R)) (hDx : DifferentiableAt ℝ w x)
    (hw : ∀ n, ∀ y ∈ closedBall c R, ContDiffAt ℝ 2 (wseq n) y)
    (hpos : ∀ y ∈ ball c R, 0 < w y)
    (hwn : ∀ y ∈ closedBall c R, 0 ≤ w y)
    (hdom : ∀ n, ∀ y ∈ closedBall c R, w y ≤ wseq n y)
    (hlim : ∀ y ∈ closedBall c R, Tendsto (fun n => wseq n y) atTop (𝓝 (w y)))
    (hx : ‖x-c‖ = R) (hwx : w x = 0) (hne : ∀ᶠ y in 𝓝 x, 0 ≤ w y)
    (L : E → (E →L[ℝ] E →L[ℝ] ℝ) →ₗ[ℝ] ℝ)
    (hL : ∀ y ∈ closedBall c R, HessianPositive (L y))
    (hlower : ∀ y ∈ closedBall c R, ∀ v : E, ell*‖v‖^2 ≤ L y (realRankOneForm v))
    (htrace : ∀ y ∈ closedBall c R, L y (realInnerForm (E := E)) ≤ Λ)
    (hsub : ∀ n, ∀ y ∈ closedBall c R,
      L y (realHessian (wseq n) y) ≤ C*(wseq n y+‖fderiv ℝ (wseq n) y‖)) : False := by
  obtain ⟨k,hk,hchoice⟩ := exists_annular_barrier_exponent hell hΛ hC hR
  have hsmall : closedBall c (R/2) ⊆ ball c R := closedBall_subset_ball (by linarith)
  have hsmallclosed : closedBall c (R/2) ⊆ closedBall c R := hsmall.trans ball_subset_closedBall
  obtain ⟨z,hz,hzmin⟩ := (isCompact_closedBall c (R/2)).exists_isMinOn
    ⟨c,mem_closedBall_self (by linarith)⟩ (hwc.mono hsmallclosed)
  have heps : 0 < w z := hpos z (hsmall hz)
  have hcompn (n : ℕ) : ∀ y ∈ closedAnnulus c R,
      w z*annularBarrier k R c y ≤ wseq n y := by
    apply compact_gradient_barrier_comparison (isCompact_closedAnnulus c R)
      (fun y hy => (hw n y hy.1).continuousAt.continuousWithinAt)
      (annularBarrier_contDiff k R c (n := 2)).continuous.continuousOn
      (fun y hy => hw n y (interior_subset hy).1)
      (fun _ _ => (annularBarrier_contDiff k R c (n := 2)).contDiffAt) L
      (fun y hy => hL y (interior_subset hy).1) hC heps
      (fun y hy => hsub n y (interior_subset hy).1)
    · intro y hy
      have hya := (mem_closedAnnulus c y R).mp (interior_subset hy)
      have hyb : y ∈ closedBall c R := (interior_subset hy).1
      exact annularBarrier_strict_subsolution (L y) c y hell hC hR hk hchoice
        (hlower y hyb (y-c)) (htrace y hyb) hya.1 hya.2
    · intro y hy hni
      have hya := (mem_closedAnnulus c y R).mp hy
      by_cases houter : ‖y-c‖ = R
      · rw [annularBarrier_zero_on_sphere k R c y houter,mul_zero]
        exact (hwn y hy.1).trans (hdom n y hy.1)
      · have hinner : ‖y-c‖ = R/2 := by
          by_contra hn
          exact hni (mem_interior_closedAnnulus
            (lt_of_le_of_ne hya.1 (Ne.symm hn)) (lt_of_le_of_ne hya.2 houter))
        have hymem : y ∈ closedBall c (R/2) := by rw [mem_closedBall,dist_eq_norm,hinner]
        have hb := mul_le_mul_of_nonneg_left (annularBarrier_le_one hk.le R c y) heps.le
        have hb' : w z*annularBarrier k R c y ≤ w z := by simpa only [mul_one] using hb
        exact hb'.trans ((hzmin hymem).trans (hdom n y hy.1))
  have hcomp : ∀ y ∈ closedAnnulus c R, w z*annularBarrier k R c y ≤ w y := by
    intro y hy
    exact le_of_tendsto_of_tendsto tendsto_const_nhds (hlim y hy.1)
      (Filter.Eventually.of_forall fun n => hcompn n y hy)
  exact annular_zero_contact_impossible hk hR heps hDx hwx hne hx
    (fun y hyl hyr => hcomp y ((mem_closedAnnulus c y R).mpr ⟨hyl,hyr⟩))

theorem zero_propagation_gradient_approximation_on_ball
    {w : E → ℝ} (wseq : ℕ → E → ℝ) {x : E} {δ ell Λ C : ℝ}
    (hδ : 0 < δ) (hell : 0 < ell) (hΛ : 0 ≤ Λ) (hC : 0 ≤ C)
    (hw : ∀ y ∈ ball x δ, DifferentiableAt ℝ w y)
    (hwseq : ∀ n, ∀ y ∈ ball x δ, ContDiffAt ℝ 2 (wseq n) y)
    (hwn : ∀ y ∈ ball x δ, 0 ≤ w y) (hwx : w x = 0)
    (hdom : ∀ n, ∀ y ∈ ball x δ, w y ≤ wseq n y)
    (hlim : ∀ y ∈ ball x δ, Tendsto (fun n => wseq n y) atTop (𝓝 (w y)))
    (L : E → (E →L[ℝ] E →L[ℝ] ℝ) →ₗ[ℝ] ℝ)
    (hL : ∀ y ∈ ball x δ, HessianPositive (L y))
    (hlower : ∀ y ∈ ball x δ, ∀ v : E, ell*‖v‖^2 ≤ L y (realRankOneForm v))
    (htrace : ∀ y ∈ ball x δ, L y (realInnerForm (E := E)) ≤ Λ)
    (hsub : ∀ n, ∀ y ∈ ball x δ,
      L y (realHessian (wseq n) y) ≤ C*(wseq n y+‖fderiv ℝ (wseq n) y‖)) :
    ∀ y ∈ ball x (δ/4), w y = 0 := by
  intro y hy
  have hyδ : y ∈ ball x δ := ball_subset_ball (by linarith) hy
  by_contra hy0
  have hypos : 0 < w y := lt_of_le_of_ne (hwn y hyδ) (Ne.symm hy0)
  let Z : Set E := closedBall x (δ/2) ∩ w ⁻¹' ({0} : Set ℝ)
  have hhalf : closedBall x (δ/2) ⊆ ball x δ := closedBall_subset_ball (by linarith)
  have hwc : ContinuousOn w (closedBall x (δ/2)) :=
    fun z hz => (hw z (hhalf hz)).continuousAt.continuousWithinAt
  have hZclosed : IsClosed Z := hwc.preimage_isClosed_of_isClosed isClosed_closedBall isClosed_singleton
  have hxZ : x ∈ Z := ⟨mem_closedBall_self (by linarith),hwx⟩
  have hZnonempty : Z.Nonempty := ⟨x,hxZ⟩
  have hyZ : y ∉ Z := fun h => hy0 h.2
  let R := infDist y Z
  have hR : 0 < R := hZclosed.notMem_iff_infDist_pos hZnonempty |>.mp hyZ
  obtain ⟨z,hz,hzd⟩ := hZclosed.exists_infDist_eq_dist hZnonempty y
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
    rw [dist_comm,dist_eq_norm] at hzd
    exact hzd.symm
  have hpositive : ∀ p ∈ ball y R, 0 < w p := by
    intro p hp
    have hpd := hballδ (ball_subset_closedBall hp)
    have hpnot : p ∉ Z := notMem_of_dist_lt_infDist (by
      change dist y p < R
      change dist p y < R at hp
      simpa only [dist_comm] using hp)
    have hpnonzero : w p ≠ 0 := fun he => hpnot ⟨hballhalf (ball_subset_closedBall hp),he⟩
    exact lt_of_le_of_ne (hwn p hpd) (Ne.symm hpnonzero)
  have hzδ : z ∈ ball x δ := hhalf hz.1
  have hnear : ∀ᶠ p in 𝓝 z, 0 ≤ w p :=
    Filter.Eventually.mono (isOpen_ball.mem_nhds hzδ) fun p hp => hwn p hp
  exact positive_ball_cannot_touch_zero_of_approximation wseq hR hell hΛ hC
    (fun p hp => (hw p (hballδ hp)).continuousAt.continuousWithinAt) (hw z hzδ)
    (fun n p hp => hwseq n p (hballδ hp)) hpositive (fun p hp => hwn p (hballδ hp))
    (fun n p hp => hdom n p (hballδ hp)) (fun p hp => hlim p (hballδ hp))
    hzR hz.2 hnear L (fun p hp => hL p (hballδ hp))
    (fun p hp => hlower p (hballδ hp)) (fun p hp => htrace p (hballδ hp))
    (fun n p hp => hsub n p (hballδ hp))

/-- Ellipticity and the gradient-inequality constant are uniform in the index. -/
def LocallyUniformApproximatingSupersolutions (U : Set E) (wseq : ℕ → E → ℝ)
    (L : E → (E →L[ℝ] E →L[ℝ] ℝ) →ₗ[ℝ] ℝ) : Prop :=
  ∀ x ∈ U, ∃ δ ell Λ C : ℝ, 0 < δ ∧ 0 < ell ∧ 0 ≤ Λ ∧ 0 ≤ C ∧
    ball x δ ⊆ U ∧
    (∀ y ∈ ball x δ, HessianPositive (L y)) ∧
    (∀ y ∈ ball x δ, ∀ v : E, ell*‖v‖^2 ≤ L y (realRankOneForm v)) ∧
    (∀ y ∈ ball x δ, L y (realInnerForm (E := E)) ≤ Λ) ∧
    (∀ n, ∀ y ∈ ball x δ,
      L y (realHessian (wseq n) y) ≤ C*(wseq n y+‖fderiv ℝ (wseq n) y‖))

theorem strong_minimum_gradient_approximation_positive {U : Set E}
    (hU : IsOpen U) (hconn : IsPreconnected U) {w : E → ℝ} (wseq : ℕ → E → ℝ)
    (hw : ∀ x ∈ U, DifferentiableAt ℝ w x)
    (hseq : ∀ n, ∀ x ∈ U, ContDiffAt ℝ 2 (wseq n) x)
    (hwn : ∀ x ∈ U, 0 ≤ w x)
    (hdom : ∀ n, ∀ x ∈ U, w x ≤ wseq n x)
    (hlim : ∀ x ∈ U, Tendsto (fun n => wseq n x) atTop (𝓝 (w x)))
    (L : E → (E →L[ℝ] E →L[ℝ] ℝ) →ₗ[ℝ] ℝ)
    (hL : LocallyUniformApproximatingSupersolutions U wseq L)
    (hanchor : ∃ x ∈ U, 0 < w x) : ∀ x ∈ U, 0 < w x := by
  apply positive_on_connected_of_local_zero_propagation hU hconn
    (fun x hx => (hw x hx).continuousAt.continuousWithinAt) hwn ?_ hanchor
  intro x hx hx0
  obtain ⟨δ,ell,Λ,C,hδ,hell,hΛ,hC,hball,hpos,hlower,htrace,hsub⟩ := hL x hx
  have hh := zero_propagation_gradient_approximation_on_ball wseq hδ hell hΛ hC
    (fun y hy => hw y (hball hy)) (fun n y hy => hseq n y (hball hy))
    (fun y hy => hwn y (hball hy)) hx0 (fun n y hy => hdom n y (hball hy))
    (fun y hy => hlim y (hball hy)) L hpos hlower htrace hsub
  exact Filter.Eventually.mono (ball_mem_nhds x (by positivity : 0 < δ/4)) hh

end PowerConvexity
