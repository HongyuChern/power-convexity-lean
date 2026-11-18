import PowerConvexity.Calculus.QuadraticHessianFromValues
import PowerConvexity.Calculus.PoissonIntegralHessianBoundsFour

/-! # Passage from shrinking-ball quadratic approximation to the actual Hessian.
Only the actual C2 germ is used. Its actual Taylor remainder is controlled on
all sufficiently small closed balls, then the actual quadratic difference
controls the difference of the actual Hessians.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
local notation "E" => DeGiorgi.AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_C2_small_ball_secondTaylor_error_two {w : E → ℝ}
    (hw : ContDiffAt ℝ 2 w 0) {η : ℝ} (hη : 0 < η) :
    ∃ R > 0, ∀ s > 0, s ≤ R → ∀ x ∈ closedBall (0 : E) s,
      |w x-secondTaylorPolynomialZero w x| ≤ η*s^2 := by
  have hH : ContinuousAt (realHessian w) 0 :=
    ((hw.fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)).continuousAt
  have hb : ∀ᶠ x in 𝓝 (0 : E), ‖realHessian w x-realHessian w 0‖ < η := by
    have hd := (Metric.tendsto_nhds.mp hH) η hη
    simpa only [dist_eq_norm] using hd
  obtain ⟨d,hd,hdB⟩ := Metric.mem_nhds_iff.mp ((hw.eventually (by simp)).and hb)
  refine ⟨d/2,half_pos hd,?_⟩
  intro s hs hsR
  have hsub : closedBall (0 : E) s ⊆ ball 0 d :=
    closedBall_subset_ball (hsR.trans_lt (by linarith only [hd]))
  exact actual_secondTaylor_error_of_hessian_modulus hs hη.le
    (fun x hx => (hdB (hsub hx)).1) (fun x hx => (hdB (hsub hx)).2.le)

theorem actual_Hessian_norm_from_quadratic_approximation_two {w : E → ℝ} {K : ℝ}
    (hw : ContDiffAt ℝ 2 w 0) (hK : 0 ≤ K)
    (R δ : ℕ → ℝ) (hR : ∀ n, 0 < R n) (hδ : ∀ n, 0 ≤ δ n)
    (hR0 : Tendsto R atTop (𝓝 0)) (hδ0 : Tendsto δ atTop (𝓝 0))
    (hq : ∀ n, ∃ q : E → ℝ, IsQuadraticPolynomial q ∧ ‖realHessian q 0‖ ≤ K ∧
      ∀ x ∈ closedBall (0 : E) (R n), |w x-q x| ≤ δ n*(R n)^2) :
    ‖realHessian w 0‖ ≤ K := by
  apply le_of_forall_pos_le_add
  intro η hη
  obtain ⟨s,hs,hTaylor⟩ := actual_C2_small_ball_secondTaylor_error_two hw
    (by positivity : (0:ℝ)<η/16)
  obtain ⟨N,hNs,hNδ⟩ := ((hR0.eventually (gt_mem_nhds hs)).and
    (hδ0.eventually (gt_mem_nhds (by positivity : (0:ℝ)<η/16)))).exists
  obtain ⟨q,hqq,hqH,hqa⟩ := hq N
  have hT := secondTaylorPolynomialZero_isQuadratic hw
  have hFq := IsQuadraticPolynomial_sub hT hqq
  have hFb (x : E) (hx : x ∈ closedBall 0 (R N)) :
      |secondTaylorPolynomialZero w x-q x| ≤ (η/16+δ N)*(R N)^2 := by
    calc
      _ ≤ |secondTaylorPolynomialZero w x-w x|+|w x-q x| := by
        simpa only [sub_add_sub_cancel] using
          abs_add_le (secondTaylorPolynomialZero w x-w x) (w x-q x)
      _ ≤ (η/16)*(R N)^2+δ N*(R N)^2 := add_le_add
        (by simpa only [abs_sub_comm] using hTaylor (R N) (hR N) hNs.le x hx) (hqa x hx)
      _ = _ := by ring
  have hFH := quadratic_hessian_norm_bound_from_scaled_sup hFq (hR N)
    (add_nonneg (by positivity) (hδ N)) hFb
  rw [realHessian_sub_at (IsQuadraticPolynomial_contDiff hT 2).contDiffAt
    (IsQuadraticPolynomial_contDiff hqq 2).contDiffAt,secondTaylorPolynomialZero_hessian hw] at hFH
  have hh : ‖realHessian w 0‖ ≤ 8*(η/16+δ N)+K := by
    calc
      _ = ‖(realHessian w 0-realHessian q 0)+realHessian q 0‖ := by
        have he : (realHessian w 0-realHessian q 0)+realHessian q 0 = realHessian w 0 := by
          ext v z
          simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.sub_apply]
          ring
        exact congrArg (fun H : E →L[ℝ] E →L[ℝ] ℝ => ‖H‖) he.symm
      _ ≤ ‖realHessian w 0-realHessian q 0‖+‖realHessian q 0‖ :=
        norm_add_le (realHessian w 0-realHessian q 0) (realHessian q 0)
      _ ≤ _ := add_le_add hFH hqH
  linarith only [hh,hNδ]

end PowerConvexity
